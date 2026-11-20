//! Lab persistence only. No product database or network interface.
use openmls_rust_crypto::RustCrypto;
use openmls_sqlite_storage::{Codec, SqliteStorageProvider};
use openmls_traits::OpenMlsProvider;
use rusqlite::{Connection, functions::FunctionFlags};
use serde::{Serialize, de::DeserializeOwned};
use std::{
    io::Write as _,
    path::Path,
    sync::{Arc, Mutex},
    time::Duration,
};

pub(crate) type Result<T> = std::result::Result<T, String>;

pub(crate) fn checked<T, E>(result: std::result::Result<T, E>, stage: &str) -> Result<T> {
    result.map_err(|_| stage.to_owned())
}

#[derive(Default)]
pub(crate) struct JsonCodec;
impl Codec for JsonCodec {
    type Error = serde_json::Error;
    fn to_vec<T: Serialize>(value: &T) -> std::result::Result<Vec<u8>, Self::Error> {
        serde_json::to_vec(value)
    }
    fn from_slice<T: DeserializeOwned>(bytes: &[u8]) -> std::result::Result<T, Self::Error> {
        serde_json::from_slice(bytes)
    }
}

pub(crate) struct Provider<'a> {
    crypto: RustCrypto,
    storage: SqliteStorageProvider<JsonCodec, &'a Connection>,
}
impl<'a> Provider<'a> {
    pub(crate) fn new(connection: &'a Connection) -> Self {
        Self {
            crypto: RustCrypto::default(),
            storage: SqliteStorageProvider::new(connection),
        }
    }
}
impl<'a> OpenMlsProvider for Provider<'a> {
    type CryptoProvider = RustCrypto;
    type RandProvider = RustCrypto;
    type StorageProvider = SqliteStorageProvider<JsonCodec, &'a Connection>;
    fn crypto(&self) -> &RustCrypto {
        &self.crypto
    }
    fn rand(&self) -> &RustCrypto {
        &self.crypto
    }
    fn storage(&self) -> &Self::StorageProvider {
        &self.storage
    }
}

pub(crate) fn open(path: &Path) -> Result<Connection> {
    let connection = checked(Connection::open(path), "sqlite_open")?;
    checked(
        connection.busy_timeout(Duration::from_secs(10)),
        "sqlite_timeout",
    )?;
    checked(
        connection.execute_batch(
            "PRAGMA foreign_keys=ON; PRAGMA journal_mode=DELETE; PRAGMA synchronous=FULL;",
        ),
        "sqlite_pragmas",
    )?;
    Ok(connection)
}

pub(crate) fn initialize(connection: &mut Connection) -> Result<()> {
    checked(
        SqliteStorageProvider::<JsonCodec, &mut Connection>::new(connection).run_migrations(),
        "provider_migrations",
    )?;
    checked(connection.execute_batch("CREATE TABLE shell_state (singleton INTEGER PRIMARY KEY CHECK(singleton=1), checkpoint BLOB NOT NULL, state BLOB NOT NULL);
        CREATE TABLE shell_peer (leg INTEGER PRIMARY KEY, state BLOB NOT NULL);
        CREATE TABLE shell_receipt (operation_id TEXT PRIMARY KEY, parent BLOB NOT NULL UNIQUE, checkpoint BLOB NOT NULL UNIQUE, request BLOB NOT NULL, receipt BLOB NOT NULL);
        CREATE TABLE shell_outbox (operation_id TEXT PRIMARY KEY REFERENCES shell_receipt(operation_id) DEFERRABLE INITIALLY DEFERRED, receipt BLOB NOT NULL);"), "shell_schema")
}

pub(crate) fn transaction<T>(
    connection: &Connection,
    action: impl FnOnce() -> Result<T>,
) -> Result<T> {
    checked(connection.execute_batch("BEGIN IMMEDIATE"), "begin")?;
    match action() {
        Ok(value) => match checked(connection.execute_batch("COMMIT"), "commit") {
            Ok(()) => Ok(value),
            Err(error) => {
                let _ = connection.execute_batch("ROLLBACK");
                Err(error)
            }
        },
        Err(error) => {
            let _ = connection.execute_batch("ROLLBACK");
            Err(error)
        }
    }
}

#[derive(Clone, Default)]
pub(crate) struct Boundaries(Arc<Mutex<Vec<String>>>);
impl Boundaries {
    pub(crate) fn labels(&self) -> Vec<String> {
        self.0.lock().expect("boundary mutex").clone()
    }
}

pub(crate) fn install_failpoints(
    connection: &Connection,
    abort_at: Option<usize>,
) -> Result<Boundaries> {
    let boundaries = Boundaries::default();
    let recorded = boundaries.clone();
    checked(
        connection.create_scalar_function(
            "shell_boundary",
            1,
            FunctionFlags::SQLITE_UTF8,
            move |context| {
                let label: String = context.get(0)?;
                let mut entries = recorded.0.lock().expect("boundary mutex");
                entries.push(label.clone());
                let index = entries.len();
                if abort_at == Some(index) {
                    println!("CRASH_AT={index}:{label}");
                    let _ = std::io::stdout().flush();
                    std::process::abort();
                }
                Ok(0_i64)
            },
        ),
        "install_failpoint",
    )?;
    let mut statement = checked(connection.prepare("SELECT name FROM sqlite_master WHERE type='table' AND (name LIKE 'openmls_%' OR name LIKE 'shell_%') ORDER BY name"), "tables")?;
    let tables = checked(
        checked(
            statement.query_map([], |row| row.get::<_, String>(0)),
            "table_query",
        )?
        .collect::<std::result::Result<Vec<_>, _>>(),
        "table_rows",
    )?;
    drop(statement);
    for (index, table) in tables.iter().enumerate() {
        let quoted = table.replace('"', "\"\"");
        for operation in ["INSERT", "UPDATE", "DELETE"] {
            for timing in ["BEFORE", "AFTER"] {
                let label = format!("{table}/{operation}/{timing}");
                checked(connection.execute_batch(&format!("CREATE TEMP TRIGGER fail_{index}_{operation}_{timing} {timing} {operation} ON \"{quoted}\" BEGIN SELECT shell_boundary('{label}'); END;")), "trigger")?;
            }
        }
    }
    Ok(boundaries)
}

pub(crate) fn before_commit(connection: &Connection) -> Result<()> {
    checked(
        connection.query_row("SELECT shell_boundary('COMMIT/BEFORE')", [], |row| {
            row.get::<_, i64>(0)
        }),
        "precommit_boundary",
    )
    .map(|_| ())
}

/// Clone ONLY the canonical device's published SQLite storage tables, never
/// the separate peer's private state. Used exclusively for exposure controls.
#[cfg(test)]
pub(crate) fn snapshot(connection: &Connection) -> Connection {
    let clone = Connection::open_in_memory().unwrap();
    let mut tables = connection.prepare("SELECT name, sql FROM sqlite_master WHERE type='table' AND name LIKE 'openmls_%' ORDER BY name").unwrap();
    let tables: Vec<(String, String)> = tables
        .query_map([], |row| Ok((row.get(0)?, row.get(1)?)))
        .unwrap()
        .map(std::result::Result::unwrap)
        .collect();
    for (name, schema) in tables {
        clone.execute_batch(&schema).unwrap();
        let quoted = name.replace('"', "\"\"");
        let mut rows = connection
            .prepare(&format!("SELECT * FROM \"{quoted}\""))
            .unwrap();
        let columns = rows.column_count();
        let placeholders = vec!["?"; columns].join(",");
        let insert = format!("INSERT INTO \"{quoted}\" VALUES ({placeholders})");
        let values = rows
            .query_map([], |row| {
                (0..columns)
                    .map(|i| row.get::<_, rusqlite::types::Value>(i))
                    .collect::<std::result::Result<Vec<_>, _>>()
            })
            .unwrap();
        for value in values {
            clone
                .execute(&insert, rusqlite::params_from_iter(value.unwrap()))
                .unwrap();
        }
    }
    clone
}
