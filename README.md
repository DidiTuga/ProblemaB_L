# ProblemaB_L 2021/2022

O objetivo deste problema é, dada uma fórmula de lógica proposicional, construir uma
BDD que a represente. Após contruir a BDD, averiguar qual a solução lexicográficamente mais pequena que resulta na avaliação da fórmula f em verdade, bem como contar o número de soluções diferentes que esta possui.

### Input

* Primeira linha: valor k (0 < k ≤ 16) que indica o número de variáveis da fórmula de lógica proposicional f.

* Segunda linha: uma fórmula f de lógica proposicional.

### Output

* Primeira linha: string com a valoração lexicograficamente mais baixa que torna a fórmula f verdadeira, ou a string NONE caso não exista nenhuma valoração que torne f verdadeira.

* Segunda linha: inteiro que represente o número de valorações que tornam a fórmula f verdadeira.

* Terceira linha: inteiro que represente o número de folhas da BDD resultante.

Para formar as fórmulas, deverá associar a cada variável xi de f um inteiro, começando com x1 → 0 até x16 → 15.

*Input exemplo*

3
((0 & 1) -> 2)

*Output exemplo*

000
7
4
