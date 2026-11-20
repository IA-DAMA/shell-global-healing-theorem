# F4 global · L1 · exposição do processo durante `prepare`

## Escopo e identidade

Product fixado em `476bd8f1f4755ae2f6a689d23a937ba2573434a4`.
O módulo formal desta etapa é `formal/easycrypt/F4_L1_Process_Window.ec`.
Esta nota não generaliza a conclusão para `apply`, `Welcome`, `resync`, retry,
crash ou múltiplas instalações; essas são obrigações de L2 e seguintes.

## Resultado da tentativa de refutação

A primeira hipótese atacada foi: “uma exposição durante a preparação ainda
poderia deixar fresca a própria época sucessora”. Ela é falsa no Product
fixado. O grupo pendente contém o estado sucessor e seus segredos de época. A
exposição integral do processo enquanto esse objeto está vivo entrega uma
capacidade para a época sucessora. Portanto essa época é `Bad_epoch`, não um
desafio admissível. Isso é a semântica usual de PCS após corrupção, não uma
quebra da primitiva.

Também foi atacada a hipótese de que rollback de SQL restauraria o objeto Rust.
O código faz o merge do commit no objeto `group` e só depois reverte o
savepoint; o rollback afeta a conexão, não rebobina o valor Rust. A observação
sintética anteriormente registrada confirma a época sucessora em memória após
o rollback. O novo resultado abaixo fixa a duração tipada desse objeto no MIR.

## Fronteiras de fonte

No arquivo
`research/protocol_shell/pq_group_chat_lab/src/offline_product_lifecycle.rs`:

- linhas 325–326 carregam `group` e o signer;
- linhas 327–350 constroem o corpo da operação;
- linhas 354–382 criam o commit, inclusive `remove_members`;
- linhas 384–392 serializam o commit público e leem o contexto do
  `pending_commit`;
- linhas 393–396 criam o savepoint;
- linhas 397–403 fazem `merge_pending_commit` e exportam o `group_info` do
  sucessor;
- linhas 404–407 fazem rollback e release do savepoint;
- linha 408 conserva o `group_info` no corpo;
- linhas 409–416 assinam a requisição;
- linhas 418–424 persistem a preparação local.

No OpenMLS vendorizado:

- `third_party/openmls-0.9.0/src/group/mls_group/staged_commit.rs`, linhas
  1103–1109: `MemberStagedCommitState` contém `group_epoch_secrets`,
  `message_secrets` e novos pares de chave;
- no mesmo arquivo, linhas 535–604: a preparação deriva os segredos da nova
  época e monta o estado staged;
- no mesmo arquivo, linhas 1067–1096: o exportador staged deriva de
  `group_epoch_secrets.exporter_secret`;
- `third_party/openmls-0.9.0/src/group/mls_group/exporting.rs`, linhas 35–52:
  o exportador instalado deriva do segredo da época instalado;
- `third_party/openmls-0.9.0/src/ciphersuite/secret.rs`, linhas 13–16: `Secret`
  guarda bytes secretos e, na revisão fixada, não implementa `Drop` com
  zeroização.

O provider de `openmls_rust_crypto` contém `ChaCha20Rng` e o inicializa por
`from_entropy`. A custódia Android conserva, durante a operação, uma cópia em
`Zeroizing<[u8;64]>`. O signer carregado pelo Product contém a chave privada.
Consequentemente uma exposição integral do processo não pode ser modelada como
“somente o estado MLS”: inclui também provider/RNG, signer e a cópia de
custódia enquanto estiverem vivos.

## Liveness MIR e cortes

O compilador fixou os locais de debug da closure de `prepare` como:

| valor | local MIR | `StorageLive` | `StorageDead`, caminhos normais/cleanup |
|---|---:|---:|---:|
| `group` | `_112` | linha 325 | linha 425 |
| `signer` | `_123` | linha 326 | linha 425 |
| corpo `b` | `_134` | linha 327 | linha 425 |
| `commit` | `_202` | linha 354 | linha 425 |
| `probe` | `_328` | linha 397 | linha 425 |
| `request` | `_358` | linha 409 | linha 425 |

`StorageLive`/`StorageDead` prova a duração do armazenamento tipado; não prova
que bytes liberados sejam fisicamente recuperáveis nem que tenham sido
sobrescritos. A ausência de zeroizing `Drop` para `Secret` impede alegar
apagamento garantido, mas também não autoriza alegar leitura pós-liberação sem
um modelo de memória física.

| corte | valores inicializados e vivos relevantes | classificação |
|---|---|---|
| t1, após criar o commit pendente | grupo predecessor com `pending_commit`; estado e exportador sucessores no staged state; RNG; signer; custódia; commit/contexto públicos | exposição torna e+1 ruim |
| t2, após merge temporário | grupo sucessor instalado; exportador sucessor; RNG; signer; custódia; commit/contexto públicos; possíveis remanescentes não zeroizados | exposição torna e+1 ruim |
| t3, após rollback do savepoint | mesmo objeto Rust sucessor; `group_info` público; demais valores de t2 | rollback não cura e+1 |
| t4, erro/unwind/interrupção | depende do contador de programa: `T4Pending`, `T4Merged` ou `T4Rolled` | não existe um único conjunto correto para t4 |
| t5a, restart antes do commit SQL | objetos tipados anteriores não existem; ao recarregar, o estado durável continua no predecessor | sucessor anterior não é atribuído ao novo processo |
| t5b, restart depois do commit SQL | o storage OpenMLS contém o grupo com commit pendente; `require_pending` o recarrega e verifica seu contexto sucessor | exposição do novo processo torna e+1 ruim outra vez |

O ledger `gamma` no módulo formal inclui, para t1–t4 e t5b, estado e exportador
sucessores, RNG, signer, custódia e os artefatos públicos aplicáveis. Em t5a
inclui o predecessor recarregado, sem atribuir ao novo processo o sucessor
volátil perdido. Nenhum dos dois cortes t5 afirma observabilidade de
remanescente físico do processo morto.

## Decisão de ameaça e cura

Definição operacional desta etapa:

`Bad_epoch(e+1) := ExposeProcess` em qualquer corte onde o sucessor `e+1` está
vivo.

O módulo EasyCrypt prova no modelo:

1. todo corte tipado t1–t4 que contém o sucessor o registra em `gamma`;
2. uma exposição nesses cortes marca a época sucessora como ruim;
3. a própria época exposta não satisfaz o gate `healed`;
4. o primeiro commit posterior pode ser selecionado como cura somente se sua
   entrada for independente da vista clássica-quântica acumulada e não houver
   exposição posterior;
5. o gate não é vazio: e+1 é rejeitada e e+2 é admitida no testemunho formal.

A conclusão sobre e+2 é **condicional**. O código mostra uma nova amostragem do
path secret pelo provider, mas independência computacional da memória auxiliar
do adversário exige as hipóteses nomeadas:

- `H_next_entropy`: a amostra posterior é imprevisível para a vista
  clássica-quântica anterior, com custo `eps_env`/gerador explicitado;
- `H_no_later_exposure`: não há nova exposição relevante antes do desafio;
- `H_active_auth`: o adversário não consegue instalar um commit ativo usando
  signer/custódia expostos; com Ed25519 não se presume resistência a QPT ativo;
- hipóteses do subcaso parcial 2→1: segredo de commit uniforme e independente e
  domínio coberto pelo schedule já provado.

Sob essas hipóteses, a composição desta etapa é
`Adv <= 2d + 10h + eps_gen`, sem arredondamento. O módulo apenas compõe essa
cota parcial com `eps_gen`; não prova as vantagens concretas das primitivas nem
a independência da fonte real.

## Controle negativo e não-vacuidade

O controle remove `SuccessorState` do corte `T2Merged`. O lema
`successor_is_accounted` deixa de ser demonstrável e o verificador rejeita o
módulo mutado. Logo a cobertura do sucessor não é decorativa.

`healing_witness` exibe uma execução abstrata admitida: exposição em t2 torna
e+1 ruim; e+1 não é cura; um primeiro commit independente posterior permite
selecionar e+2. Isso prova não-vacuidade do gate, não a ocorrência das hipóteses
no Product real.

## Rótulos e primeira afirmação ainda não demonstrada

- **PROVADO_KERNEL (modelo L1):** cobertura do sucessor em `gamma`, rejeição da
  época exposta, gate temporal, composição algébrica condicional e testemunho
  não-vazio.
- **PROVADO_PAPEL + MODELO_TESTADO (ponte local):** mapeamento dos valores Rust,
  campos OpenMLS, liveness MIR e rollback que não rebobina o objeto Rust.
- **ABERTO (CC físico completo):** não está demonstrado que toda capacidade
  observável numa exposição física de processo — inclusive cópias internas de
  alocador, registradores, temporários criptográficos, dumps e material que
  possa abrir cópias futuras — esteja contida em `gamma`.

A primeira afirmação não demonstrada é:

> Para toda execução e todo corte físico de `prepare`, a observação integral do
> processo é simulável a partir de `gamma(corte)` sem perder correlações com a
> memória auxiliar quântica do adversário.

Essa é uma obrigação de refinamento, não uma conclusão que possa ser obtida da
contabilidade de posse em Lean. O resultado atual fecha a classificação da
época sucessora e torna explícitas as hipóteses mínimas de cura; não fecha ainda
CC universal nem a F4 global.
