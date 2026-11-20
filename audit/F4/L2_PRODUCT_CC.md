# F4 global · L2 · cobertura operacional do Product

## Resultado

L2 foi fechada como barreira conservadora de cobertura para o Product fixado
em `476bd8f1f4755ae2f6a689d23a937ba2573434a4`. Ela não certifica uma operação
desconhecida por ausência de evidência: toda transição recebe uma semântica
provada ou cria uma lacuna irreversível que impede admissão do desafio.

## Escopo nativo exaustivo

O verificador `verify_l2_source_scope.py` comparou três fronteiras:

1. as 34 variantes declaradas em `ProductRequest`;
2. as 34 variantes tratadas pelo dispatcher `execute_android`;
3. as 34 variantes do classificador `f4_native_request_obligation`.

Os conjuntos são idênticos. O classificador não possui braço wildcard. Os
hashes observados foram:

- `offline_product.rs`:
  `0eaabf8e3228e68541c0d09f4bdc294cb7a011f504a289e5b2399328616eb045`;
- `offline_product_f4_request_scope.rs`:
  `5f3017e8c6362ac06a2d35d2822ad814a153b9752fbcf994c13aab1a2941973c`;
- `offline_product_f4_semantic_audit.rs`:
  `aede3405a604836016f5f5300212c6915df3942068f517f41305b8a24810d2c9`.

Uma variante futura exige alterar o match exaustivo ou a build falha. Isso
prova cobertura sintática da revisão, não semântica secreta de cada callee.

## Indução e classes

`F4_CC_Observation_Prefix.ec` já prova individualmente e por indução arbitrária
as doze classes: captura antiga, prepare, apply, snapshot, Welcome, resync,
erro de remoção, crash, restart, retry, cópia de aparelho e concessão. O modelo
mantém separadas capacidades duráveis, staged, remotas e adquiridas.

`F4_L2_Product_CC.ec` compõe essa indução com:

- a cobertura de processo de L1 em cada corte de `prepare`;
- o classificador nativo exaustivo;
- a barreira de cobertura da fonte.

Somente leitura pública verificada, commit filho verificado e instalação
same-head/same-epoch verificada recebem certificado de passo. Rejeições com
estado público igual, mutações privadas possíveis, instalações não refinadas,
Welcome e resync sem certificado não são tratados como stutter. Eles marcam
`coverage_gap=false` de forma monotônica e permanecem fora de `Adm` em todo
sufixo.

## Não-vacuidade

O testemunho formal contém captura antiga, preparação, estado durável após
erro de remoção, crash e restart. Esse prefixo é admitido. Uma concessão
posterior, cópia entre aparelhos e retry tornam o alvo derivável e portanto
inelegível. Assim a barreira não rejeita todas as execuções, mas rejeita a
combinação que realmente entrega a saída.

## Revisão hostil e controles

- Omitir qualquer uma das doze classes do ledger produz um caminho finito de
  divergência; os doze controles foram rejeitados.
- Fazer rollback apagar RAM invalida o lema do savepoint.
- Omitir o sucessor no corte t2 invalida L1.
- Permitir que um passo posterior apague uma lacuna de cobertura invalida
  `f4_sa_gap_never_disappears_under_any_finite_suffix`.

## Classificação

- **PROVADO_KERNEL:** indução sobre todas as listas finitas do modelo,
  composição com L1, monotonicidade da lacuna e não-vacuidade.
- **PROVADO_PAPEL / MODELO_TESTADO:** enum/dispatcher/classificador exaustivos
  na revisão Rust fixada e testes nativos já exercitados pelo replay.
- **Limite explícito:** histories com Welcome, resync ou efeito privado sem
  certificado não recebem alegação de cura; ficam fora de `Adm`. L2 prova que
  isso ocorre de modo fail-closed, não a segurança dessas rotas. Cobri-las com
  massa positiva exige refinar suas semânticas, não remover a barreira.
