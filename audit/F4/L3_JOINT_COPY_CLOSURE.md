# L3 — fecho conjunto das cópias

## Resultado

`F4_L3_Joint_Copy_Closure.ec` liga as doze classes do modelo operacional de
L2 ao certificado temporal linear já existente. Para cada operação, a linha
usa coordenadas booleanas e satisfaz exatamente:

`0 <= y_i <= 1`, `x_i <= y_i` e `y_a + y_b - y_c <= 1`.

O único arco conjunto desta abstração exige as duas capacidades, `Blob` e
`Key`, ainda que venham de instalações e instantes diferentes. `Resync` e
`Retry` são os únicos passos que executam essa junção; estando o processo
offline, a regra não é habilitada.

## Provas

- `l3_each_l2_case_row`: instância calculável para cada uma das doze classes;
- `l3_trace_linear_certificate`: certificado por indução para todo prefixo
  finito cuja visão final não contém a saída;
- `l3_trace_symbolic_cut`: conversão exata da matriz para ausência de rota no
  fecho temporal;
- `l3_nonvacuous_old_capture_is_admitted`: captura antiga, preparação,
  persistência com erro, crash/restart, snapshot e retry sem concessão;
- `l3_cross_install_combination_reaches_output`: Welcome e concessão reunidos
  de outro aparelho chegam à saída depois do retry;
- `l3_cross_install_combination_is_recorded`: a mesma saída aparece no ledger.

## Alcance

Este fechamento é a sobreaproximação simbólica exigida pela correção C1 de
`GLOBAL_V1.md`. Ele não identifica ausência de rota com indistinguibilidade
computacional. A redução QPT, memória auxiliar e perdas pertencem a L5/L6.
Operações nativas sem certificado completo permanecem fora de `Adm` por L2.

## Controle hostil

O reprodutor remove somente a concessão `Grant` da história hostil. A prova da
combinação entre instalações deve falhar em
`l3_cross_install_combination_reaches_output`. Se passar, o modelo não exige a
necessidade conjunta das duas classes de cópia.
