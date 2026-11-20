# L5 — ponte QPT black-box

## Fronteira formal

`F4_L5_QPT_Blackbox_Bridge.ec` recebe uma memória auxiliar opaca `qaux` e a
passa, na mesma execução, por gerador, HMAC, exportador e decisão final. Cada
componente devolve o único estado residual usado pelo componente seguinte.
As reduções são os sufixos inalterados do jogo: não reiniciam o adversário,
não pedem uma segunda decisão e não recuperam um estado auxiliar anterior.

O kernel prova seis equivalências exatas entre os jogos adjacentes e as
experiências de primitivas, e então:

    Adv(G0,G3) <= eps_gen + eps_hmac + eps_exporter.

`eps_gen` cobre a substituição da fonte/gerador com toda a vista auxiliar
admitida, incluindo os saltos QSF/X-Wing e o fluxo limitado do gerador quando
instanciados. `eps_hmac` cobre a orientação concreta dos Extract/Expand do key
schedule. `eps_exporter` cobre a coordenada do exportador e reaberturas. Esses
termos são hipóteses QPT de primitivas para consultas clássicas; o arquivo não
os declara pequenos por axioma nem converte automaticamente resultados
clássicos em quânticos.

## Consultas em superposição

O tipo `L5Coherent` é explicitamente recusado por `l5_admitted_mode`. Um
adversário com acesso coerente aos oráculos precisa de outro jogo, com seus
próprios termos QROM/QPRF. Nenhuma tabela clássica preguiçosa é usada como se
fosse um oráculo quântico.

## Significado da memória auxiliar

EasyCrypt trata `qaux` como tipo opaco. A leitura física como registro
quântico, e a segurança QPT dos jogos de primitivas com esse registro, são
hipóteses importadas e nomeadas. O que o kernel demonstra aqui é a estrutura
black-box, de uma passagem, sem clonagem ou rebobinamento no programa da
redução. Não é uma formalização da álgebra de operadores quânticos.

## Não-vacuidade e controle negativo

Consultas clássicas formam um construtor admitido e consultas coerentes não.
O controle negativo faz `L5G1` descartar o residual do gerador e reutilizar o
estado inicial no HMAC. A equivalência `l5_g1_generator_ideal_exact` deve
falhar; se passasse, o encadeamento de memória seria vácuo.
