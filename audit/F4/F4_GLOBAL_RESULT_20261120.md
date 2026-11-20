# Shell F4 — resultado global de 20/11/2026

## Estado

**A — PROVADO_KERNEL sob hipóteses nomeadas.**

Para todo adversário QPT admissível, com memória auxiliar quântica e somente
consultas clássicas ao Product, o conjunto formal prova:

```text
Adv_F4(A) <= eps_PQ + eps_ref + Pr[Bad_CC] + eps_svc + eps_env
eps_PQ    =  eps_gen + eps_hmac + eps_exporter
```

O resultado é condicional por construção. Ele não afirma que todos os termos
são desprezíveis na implantação atual. Em particular, Ed25519 não fornece uma
hipótese de autenticação contra um adversário QPT ativo; esse limite permanece
explicitamente em `eps_svc`.

## O que foi fechado

- **C1:** frescor computacional e classe admissível; o fecho simbólico é apenas
  uma sobreaproximação suficiente.
- **L1:** janela de exposição do processo; uma época cujo sucessor vivo foi
  exposto é marcada como exposta, e a cura posterior exige contribuição nova,
  independente e não exposta.
- **L2:** cobertura fail-closed das classes operacionais do Product.
- **L3:** fecho conjunto de cópias entre épocas e instalações, sem pressupor
  independência entre capacidades já entregues.
- **L4:** refinamento do traço Product admitido para o jogo, com divergências
  retidas como lacuna e contabilizadas por `Bad_CC`/`eps_ref`.
- **L5:** ponte QPT black-box para gerador, HMAC e exportador, com memória
  auxiliar opaca preservada, sem rebobinar ou clonar.
- **L6:** composição quantitativa final dos cinco mundos adjacentes.

## Classificação das premissas

### Provadas pelo kernel/modelo

- induções finitas de cobertura e posse;
- certificado de fecho conjunto;
- preservação da relação de refinamento no traço admitido;
- equivalências dos jogos QPT black-box e composição dos limites;
- cota global condicional acima.

### Auditadas contra a fonte fixada

- Product `476bd8f1f4755ae2f6a689d23a937ba2573434a4`;
- enumeração e despacho das classes nativas;
- cronologia e liveness tipado da janela de preparação;
- vetores Rust comparados com cálculo independente.

Essas auditorias de fonte não são uma extração total verificada de toda a
semântica Rust nem uma afirmação sobre remanência física de memória.

### Hipóteses quantitativas importadas ou ainda não instanciadas

- `eps_gen`: substituição do gerador real pelo ideal na interface e no domínio
  exatos do jogo;
- `eps_hmac`: vantagem QPT do HMAC/HKDF na orientação concreta;
- `eps_exporter`: vantagem QPT do exportador real/ideal;
- `eps_ref`: divergência residual fora do traço fonte-tipado admitido;
- `eps_svc`: autenticação/serviço, incluindo a fronteira Ed25519;
- `eps_env`: ambiente e capacidades fora do jogo modelado.

### Não afirmado

- acesso coerente, em superposição, aos oráculos do Product;
- valores numéricos concretos para todos os epsilons;
- segurança pós-quântica ativa de Ed25519;
- certificado incondicional da implantação em produção.

## Reprodução observada

No commit de prova
`0da7b9096fd859ed99d097b311505d6733f54982`, a reprodução integral terminou
com código zero em `/tmp/tmp.oZIAmK8ONC` e registrou:

- Product Rust: 1/1 teste selecionado aprovado;
- Lean 4.31.0: ponte MIR aceita e controle de aresta alterada rejeitado;
- 12 testes de contrato aprovados;
- 5 vetores Rust ↔ cálculo independente coincidentes;
- modelo pareado: 144 estados alcançáveis, sem divergência;
- EasyCrypt: `EASYCRYPT_ALL_83_ACCEPTED=true`;
- controles negativos de L1–L6 rejeitados nos lemas esperados.

Versões: EasyCrypt `r2026.09-9-g884dad7`, Lean 4.31.0
`68218e876d2a38b1985b8590fff244a83c321783`, Rust/Cargo 1.100.0 e Python
3.12.3.

## Comando único no Windows

```powershell
powershell -ExecutionPolicy Bypass -File audit/F4/reproduce_global_windows.ps1
```

Nenhum deploy, publicação ou alteração de produção faz parte deste resultado.
