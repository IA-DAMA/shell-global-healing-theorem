# L6 — teorema global condicional

## Enunciado aceito pelo kernel

Para adversários admissíveis, consultas clássicas ao Product e memória
auxiliar QPT preservada entre as ações, o arquivo
`F4_L6_Global_Conditional_Bound.ec` compõe:

    Adv_F4 <= eps_PQ + eps_ref + Pr[Bad_CC] + eps_svc + eps_env

onde:

- `eps_PQ = eps_gen + eps_hmac + eps_exporter`, pelas reduções L5;
- `eps_ref` é a divergência entre traço nativo admitido e jogo;
- `Pr[Bad_CC]` cobra qualquer observação/cópia fora do ledger;
- `eps_svc` cobre autenticação e autoridade do serviço;
- `eps_env` cobre a última fronteira de ambiente/idealização.

O teorema usa cinco mundos vizinhos e desigualdade triangular. Nenhuma
premissa é “a vantagem global já é pequena”. L1–L4 fornecem a disciplina de
cobertura e refinamento para o traço admitido; L5 fornece a aresta
criptográfica. As vantagens das primitivas e as fronteiras reais do serviço e
ambiente continuam hipóteses quantitativas nomeadas.

## Hipóteses e alcance

1. **Provado no kernel:** contabilidade C1/L1–L4 no modelo, encadeamento
   black-box L5 e composição numérica L6.
2. **Auditado na fonte fixada:** classificação fail-closed das 34 operações,
   um único dispatcher e cronologia pré/execução/pós/classificação.
3. **Importado:** segurança QPT, com informação auxiliar e consultas
   clássicas, dos jogos concretos de fonte/gerador, HMAC e exportador.
4. **Necessário para corolário ativo QPT:** autenticação pós-quântica do
   serviço ou restrição explícita do adversário. Ed25519 não descarrega esse
   termo contra forjador QPT ativo.
5. **Fora do teorema:** consultas coerentes em superposição aos oráculos do
   Product; elas exigem jogo próprio QROM/QPRF.

## Controle negativo

O reprodutor remove `eps_svc` da definição da cota. A prova principal deve
falhar. Esse controle impede que autenticação clássica desapareça da promessa
global.
