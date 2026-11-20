use shell_classical_pq_composition::{Schedule, inspect, transition};
use std::{env, path::Path};

fn main() {
    if let Err(stage) = run() {
        eprintln!("WORKER_ERROR={stage}");
        std::process::exit(2);
    }
}
fn run() -> Result<(), String> {
    let args: Vec<_> = env::args().collect();
    if args.len() != 5 {
        return Err("usage".into());
    }
    let path = Path::new(&args[1]);
    let schedule = match args[2].as_str() {
        "peer" => Schedule::PeerUpdate,
        "renew" => Schedule::ExposedLeafRenewal,
        _ => return Err("schedule".into()),
    };
    let abort: usize = args[3].parse().map_err(|_| "index")?;
    let state = inspect(path)?;
    let (_, labels) = transition(
        path,
        "matrix-operation",
        state.checkpoint,
        schedule,
        (abort > 0).then_some(abort),
        args[4] == "post",
    )?;
    println!("{}", serde_json::to_string(&labels).map_err(|_| "labels")?);
    Ok(())
}
