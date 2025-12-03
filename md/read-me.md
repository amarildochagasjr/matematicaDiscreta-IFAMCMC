# Implementação de Matemática Discreta

Aplicação em Python com interface gráfica (CustomTkinter) para auxiliar no estudo de **lógica proposicional** e **lógica de predicados** em domínios finitos.
O programa verifica argumentos, exibe tabela‑verdade alinhada, mostra árvores de prova em forma sequencial e aplica regras clássicas (leis de De Morgan, silogismos e regras de quantificadores).
Também é possível **exportar a prova em LaTeX** para gerar relatórios e documentos acadêmicos.

---

## Funcionalidades

### Lógica Proposicional

- Inserção de múltiplas premissas e conclusão.
- Geração de tabela‑verdade do argumento, com colunas centralizadas.
- Classificação da forma do argumento (Modus Ponens, Modus Tollens, silogismos, dilemas, falácias etc.).
- Geração de “árvore de prova” em formato de lista numerada:
  - cada linha mostra a fórmula, o número da linha de origem e a regra aplicada.
- Aplicação automática das **Leis de De Morgan** sobre cada premissa.
- Exportação da prova em LaTeX (`Exportar LaTeX`) quando o argumento tiver forma válida.

### Lógica de Predicados

- Escolha de **domínio finito** (por exemplo `{1,2,3}`).
- Inserção de 1 a 3 premissas com predicados unários (`P(x)`, `H(x)`, `M(x)` etc.).
- Conclusão com quantificadores `(Ax)/(forallx)` e `(Ex)/(existsx)`.
- Verificação por **enumeração em domínio finito**:
  - informa se o argumento é válido;
  - mostra um contraexemplo quando for inválido.
- Identificação de regras de quantificadores:
  - Particularização universal
  - Generalização universal
  - Particularização existencial
  - Generalização existencial
  - Silogismo de Aristóteles
- Tratamento especial da equivalência de **De Morgan em quantificadores**:
  \(\neg(\forall x)P(x) \vdash (\exists x)\neg P(x)\).
- Exportação do enunciado em LaTeX para registrar o argumento.

---

## Tecnologias utilizadas

## Tecnologias utilizadas

- **Python 3.14** – Linguagem principal do projeto, responsável pela lógica de proposições, predicados e integração de todos os módulos.
- **CustomTkinter** – Biblioteca de componentes modernos (dark mode, botões estilizados, OptionMenu etc.) construída em cima do Tkinter, usada para a interface gráfica.
- **Tkinter** – Toolkit GUI padrão do Python; fornece a base da janela, eventos e layout sobre a qual o CustomTkinter trabalha.
- **Pillow (PIL)** – Biblioteca de tratamento de imagens, usada aqui para carregar e exibir o ícone (`ifamlogo.png`) na janela principal.
- **Sympy** – Biblioteca de álgebra simbólica; pode ser usada nos módulos internos para manipular fórmulas lógicas, expressões proposicionais ou operações algébricas de forma simbólica.
- Módulos internos:
  - `interface.py` – GUI principal.
  - `proposicao.py` – lógica proposicional (tabela‑verdade, classificação, prova condicional, De Morgan).
  - `predicados.py` – lógica de predicados em domínio finito.
  - `exportar_latex.py` – geração de arquivo `.tex` com os passos da prova.

---

## Como executar

1. **Clonar ou copiar o projeto** para uma pasta local.
        https://github.com/amarildochagasjr/matematicaDiscreta-IFAMCMC.git
