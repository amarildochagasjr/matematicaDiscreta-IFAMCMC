def exportar_prova_latex(passos, caminho="prova_atual.tex", titulo="Prova do argumento"):

    linhas = [
        r"\documentclass{article}",
        r"\usepackage[utf8]{inputenc}",
        r"\usepackage{amsmath}",
        r"\begin{document}",
        fr"\section*{{{titulo}}}",
        r"\begin{align*}"
    ]

    for num, formula, justificativa in passos:
        formula_tex = formula.replace("\\", r"\\").replace("_", r"\_")
        justificativa_tex = justificativa.replace("\\", r"\\").replace("_", r"\_")

        linhas.append(
            fr"{num}.\ & {formula_tex} && \text{{{justificativa_tex}}} \\"
        )

    linhas += [
        r"\end{align*}",
        r"\end{document}"
    ]

    with open(caminho, "w", encoding="utf-8") as f:
        f.write("\n".join(linhas))