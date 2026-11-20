# L4 — refinamento Product → jogo

## Relação

`F4_L4_Product_Game_Refinement.ec` define `R` entre o ponto nativo autenticado
e o estado público do jogo: grupo, suíte, serviço, época e head. O observador
nativo executa o dispatcher real uma vez, na ordem `pre, execute, post,
classify`; o verificador fixa essa cronologia e o hash da fonte.

## Resultado formal

- leitura autenticada é stuttering real;
- instalação no mesmo head/época é stuttering apenas nessa projeção pública;
  suas cópias privadas continuam cobertas por L1–L3;
- commit aceito avança exatamente uma época e referencia o head pai;
- por indução, toda sequência finita admitida preserva `R`;
- uma divergência de cobertura é irreversível;
- uma leitura seguida de um commit aceito fornece execução não vazia.

Logo `eps_ref = 0` dentro da classe de traços fonte-tipados admitidos. Uma
operação não demonstrada não recebe esse limite: ela entra no evento
`Bad_CC` e fica fora de `Adm`. Isso não converte uma classificação pública em
prova de apagamento, frescor ou segurança de segredo.

## Fronteira de confiança

O resultado de kernel é sobre o modelo EasyCrypt. A ligação ao Product é uma
auditoria de fonte fixada no commit nativo, não uma extração total do Rust.
Ela verifica um único `execute_android`, as observações antes/depois e as
classes fail-closed; efeitos internos não observados permanecem cobertos pelas
obrigações de cópias ou por `Bad_CC`.

## Controle negativo

O reprodutor troca `old /\ good` por `good`, permitindo que um passo posterior
apague uma divergência anterior. O lema `l4_gap_never_disappears` deve falhar.
