from sympy import symbols
from sympy.logic.boolalg import And, Or, Not, Implies, Equivalent
from sympy.logic.inference import satisfiable
from pyparsing import (
    Word, alphas, oneOf, infixNotation,
    opAssoc, ParserElement
)
import itertools

ParserElement.enablePackrat()

# ---------- PARSER (pyparsing -> SymPy) ----------

def criar_parser():
    variavel = Word(alphas.upper(), exact=1)
    variavel.setParseAction(lambda t: symbols(t[0]))

    NOT  = oneOf("~ ¬")
    AND    = oneOf("& ∧")
    OR   = oneOf("| v V")
    IMP  = "->"
    BIC  = "<->"

    def operador_unario(tokens):
        _, argumento = tokens[0][0], tokens[0][1]
        return Not(argumento)

    def operador_binario(cls):
        def acao(tokens):
            argumentos = tokens[0][0::2]
            expressao = argumentos[0]
            for outro in argumentos[1:]:
                expressao = cls(expressao, outro)
            return expressao
        return acao

    expressao = infixNotation(
        variavel,
        [
            (NOT, 1, opAssoc.RIGHT, operador_unario),
            (AND,   2, opAssoc.LEFT,  operador_binario(And)),
            (OR,  2, opAssoc.LEFT,  operador_binario(Or)),
            (IMP, 2, opAssoc.RIGHT, operador_binario(Implies)),
            (BIC, 2, opAssoc.RIGHT, operador_binario(Equivalent)),
        ]
    )
    return expressao

parser = criar_parser()

def analisar_formula(texto: str):
    return parser.parseString(texto, parseAll=True)[0]

# ---------- FORMATAÇÃO BONITA ----------

def formatar_formula(expr):
    """Converte expressão SymPy para string estilo P -> Q, P v Q, ~P etc."""
    # variável proposicional (símbolo)
    if hasattr(expr, "is_Symbol") and expr.is_Symbol:
        return expr.name
    # negação
    if isinstance(expr, Not):
        return f"~{formatar_formula(expr.args[0])}"
    # conjunção
    if isinstance(expr, And):
        return " & ".join(formatar_formula(a) for a in expr.args)
    # disjunção
    if isinstance(expr, Or):
        return " v ".join(formatar_formula(a) for a in expr.args)
    # condicional
    if isinstance(expr, Implies):
        return f"{formatar_formula(expr.args[0])} -> {formatar_formula(expr.args[1])}"
    # bicondicional
    if isinstance(expr, Equivalent):
        return f"{formatar_formula(expr.args[0])} <-> {formatar_formula(expr.args[1])}"
    return str(expr)

# ---------- LEIS DE DE MORGAN ----------

def aplicar_primeira_lei_de_morgan(formula_str: str):
    expr = analisar_formula(formula_str)
    if isinstance(expr, Not) and isinstance(expr.args[0], And):
        P, Q = expr.args[0].args
        return Or(Not(P), Not(Q))
    return expr

def aplicar_segunda_lei_de_morgan(formula_str: str):
    expr = analisar_formula(formula_str)
    if isinstance(expr, Not) and isinstance(expr.args[0], Or):
        P, Q = expr.args[0].args
        return And(Not(P), Not(Q))
    return expr

def aplicar_lei_de_morgan(formula_str: str):
    expr_original = analisar_formula(formula_str)

    expr1 = aplicar_primeira_lei_de_morgan(formula_str)
    if expr1 != expr_original:
        return expr1, "Primeira Lei de De Morgan"

    expr2 = aplicar_segunda_lei_de_morgan(formula_str)
    if expr2 != expr_original:
        return expr2, "Segunda Lei de De Morgan"

    return expr_original, None

# ---------- TABELA-VERDADE ----------

def listar_variaveis(formulas):
    variaveis = set()
    for f in formulas:
        variaveis.update(f.free_symbols)
    return sorted(variaveis, key=lambda s: s.name)

def tabela_verdade(premissas_str, conclusao_str):
    premissas = [analisar_formula(p) for p in premissas_str]
    conclusao = analisar_formula(conclusao_str)
    formulas = premissas + [conclusao]

    variaveis = listar_variaveis(formulas)
    tabela = []

    for valores in itertools.product([False, True], repeat=len(variaveis)):
        ambiente = dict(zip(variaveis, valores))
        valores_premissas = [bool(p.subs(ambiente)) for p in premissas]
        valor_conclusao = bool(conclusao.subs(ambiente))
        tabela.append((ambiente, valores_premissas, valor_conclusao))

    if premissas:
        conjuncao = And(*premissas)
        argumento_valido = not satisfiable(And(conjuncao, Not(conclusao)))
    else:
        argumento_valido = bool(conclusao)

    return variaveis, tabela, argumento_valido, premissas, conclusao

# ---------- FORMAS DE INFERÊNCIA E FALÁCIAS ----------

def eh_modus_ponens(premissas_str, conclusao_str):
    if len(premissas_str) != 2:
        return False
    a, b = [analisar_formula(p) for p in premissas_str]
    conclusao = analisar_formula(conclusao_str)
    return (
        (isinstance(a, Implies) and a.args[0] == b and conclusao == a.args[1]) or
        (isinstance(b, Implies) and b.args[0] == a and conclusao == b.args[1])
    )

def eh_modus_tollens(premissas_str, conclusao_str):
    if len(premissas_str) != 2:
        return False
    a, b = [analisar_formula(p) for p in premissas_str]
    conclusao = analisar_formula(conclusao_str)
    return (
        (isinstance(a, Implies) and isinstance(b, Not) and isinstance(conclusao, Not)
         and a.args[1] == b.args[0] and a.args[0] == conclusao.args[0]) or
        (isinstance(b, Implies) and isinstance(a, Not) and isinstance(conclusao, Not)
         and b.args[1] == a.args[0] and b.args[0] == conclusao.args[0])
    )

def eh_silogismo_hipotetico(premissas_str, conclusao_str):
    if len(premissas_str) != 2:
        return False
    a, b = [analisar_formula(p) for p in premissas_str]
    conclusao = analisar_formula(conclusao_str)
    if isinstance(a, Implies) and isinstance(b, Implies) and isinstance(conclusao, Implies):
        return a.args[1] == b.args[0] and a.args[0] == conclusao.args[0] and b.args[1] == conclusao.args[1]
    if isinstance(b, Implies) and isinstance(a, Implies) and isinstance(conclusao, Implies):
        return b.args[1] == a.args[0] and b.args[0] == conclusao.args[0] and a.args[1] == conclusao.args[1]
    return False

def eh_silogismo_disjuntivo(premissas_str, conclusao_str):
    if len(premissas_str) != 2:
        return False
    a, b = [analisar_formula(p) for p in premissas_str]
    conclusao = analisar_formula(conclusao_str)
    for disj, neg in [(a, b), (b, a)]:
        if isinstance(disj, Or) and isinstance(neg, Not):
            X, Y = disj.args
            if neg.args[0] == X and conclusao == Y:
                return True
            if neg.args[0] == Y and conclusao == X:
                return True
    return False

def eh_dilema_construtivo(premissas_str, conclusao_str):
    conclusao = analisar_formula(conclusao_str)

    if len(premissas_str) == 3:
        cond1, cond2, disj = [analisar_formula(p) for p in premissas_str]
        if isinstance(cond1, Implies) and isinstance(cond2, Implies) and \
           isinstance(disj, Or) and isinstance(conclusao, Or):
            P, Q = cond1.args
            R, S = cond2.args
            X, Y = disj.args
            C1, C2 = conclusao.args
            if {X, Y} == {P, R} and {C1, C2} == {Q, S}:
                return True
        return False

    if len(premissas_str) == 2:
        conj, disj = [analisar_formula(p) for p in premissas_str]
        if isinstance(conj, And) and isinstance(disj, Or) and isinstance(conclusao, Or):
            part1, part2 = conj.args
            if isinstance(part1, Implies) and isinstance(part2, Implies):
                P, Q = part1.args
                R, S = part2.args
                X, Y = disj.args
                C1, C2 = conclusao.args
                if {X, Y} == {P, R} and {C1, C2} == {Q, S}:
                    return True
        return False

    return False

def eh_afirmacao_consequente(premissas_str, conclusao_str):
    if len(premissas_str) != 2:
        return False
    a, b = [analisar_formula(p) for p in premissas_str]
    conclusao = analisar_formula(conclusao_str)
    return (
        (isinstance(a, Implies) and b == a.args[1] and conclusao == a.args[0]) or
        (isinstance(b, Implies) and a == b.args[1] and conclusao == b.args[0])
    )

def eh_negacao_antecedente(premissas_str, conclusao_str):
    if len(premissas_str) != 2:
        return False
    a, b = [analisar_formula(p) for p in premissas_str]
    conclusao = analisar_formula(conclusao_str)
    return (
        (isinstance(a, Implies) and isinstance(b, Not) and isinstance(conclusao, Not)
         and b.args[0] == a.args[0] and conclusao.args[0] == a.args[1]) or
        (isinstance(b, Implies) and isinstance(a, Not) and isinstance(conclusao, Not)
         and a.args[0] == b.args[0] and conclusao.args[0] == b.args[1])
    )

def eh_simplificacao(premissas_str, conclusao_str):
    if len(premissas_str) != 1:
        return False
    conj = analisar_formula(premissas_str[0])
    conclusao = analisar_formula(conclusao_str)
    if isinstance(conj, And):
        return conclusao in conj.args
    return False

def eh_conjuncao(premissas_str, conclusao_str):
    if len(premissas_str) != 2:
        return False
    a, b = [analisar_formula(x) for x in premissas_str]
    conclusao = analisar_formula(conclusao_str)
    return isinstance(conclusao, And) and set(conclusao.args) == {a, b}

def eh_adicao(premissas_str, conclusao_str):
    if len(premissas_str) != 1:
        return False
    prem = analisar_formula(premissas_str[0])
    conclusao = analisar_formula(conclusao_str)
    if isinstance(conclusao, Or):
        return prem in conclusao.args
    return False

def eh_exportacao(premissas_str, conclusao_str):
    if len(premissas_str) != 1:
        return False
    expr = analisar_formula(premissas_str[0])
    conclusao = analisar_formula(conclusao_str)
    if isinstance(expr, Implies) and isinstance(expr.args[0], And):
        P, Q = expr.args[0].args
        R = expr.args[1]
        if isinstance(conclusao, Implies) and conclusao.args[0] == P \
           and isinstance(conclusao.args[1], Implies):
            return (conclusao.args[1].args[0] == Q and conclusao.args[1].args[1] == R)
    return False

def eh_transposicao(premissas_str, conclusao_str):
    if len(premissas_str) != 1:
        return False
    expr = analisar_formula(premissas_str[0])
    conclusao = analisar_formula(conclusao_str)
    if isinstance(expr, Implies) and isinstance(conclusao, Implies):
        if isinstance(conclusao.args[0], Not) and isinstance(conclusao.args[1], Not):
            P, Q = expr.args
            return conclusao.args[0].args[0] == Q and conclusao.args[1].args[0] == P
    return False

def eh_absorcao(premissas_str, conclusao_str):
    if len(premissas_str) != 1:
        return False
    expr = analisar_formula(premissas_str[0])
    conclusao = analisar_formula(conclusao_str)
    if isinstance(expr, Implies) and isinstance(conclusao, Implies):
        P, Q = expr.args
        if conclusao.args[0] == P and isinstance(conclusao.args[1], Or):
            return P in conclusao.args[1].args and Q in conclusao.args[1].args
    return False

# ---------- CLASSIFICADOR ----------

def classificar_argumento(premissas_str, conclusao_str):
    if eh_modus_ponens(premissas_str, conclusao_str):
        return "Modus Ponens"
    if eh_modus_tollens(premissas_str, conclusao_str):
        return "Modus Tollens"
    if eh_silogismo_hipotetico(premissas_str, conclusao_str):
        return "Silogismo Hipotético"
    if eh_silogismo_disjuntivo(premissas_str, conclusao_str):
        return "Silogismo Disjuntivo"
    if eh_dilema_construtivo(premissas_str, conclusao_str):
        return "Dilema Construtivo"
    if eh_afirmacao_consequente(premissas_str, conclusao_str):
        return "Falácia: Afirmação do Consequente"
    if eh_negacao_antecedente(premissas_str, conclusao_str):
        return "Falácia: Negação do Antecedente"
    if eh_simplificacao(premissas_str, conclusao_str):
        return "Simplificação"
    if eh_conjuncao(premissas_str, conclusao_str):
        return "Introdução da Conjunção"
    if eh_adicao(premissas_str, conclusao_str):
        return "Adição (Introdução da Disjunção)"
    if eh_exportacao(premissas_str, conclusao_str):
        return "Exportação"
    if eh_transposicao(premissas_str, conclusao_str):
        return "Transposição/Contraposição"
    if eh_absorcao(premissas_str, conclusao_str):
        return "Absorção"
    return "Forma não reconhecida"

def gerar_justificativa(forma: str) -> str:
    d = {
        "Modus Ponens":
            "Se P → Q é verdadeira e P é verdadeira, então Q é verdadeira.",
        "Modus Tollens":
            "Se P → Q é verdadeira e Q é falsa, então P é falsa.",
        "Silogismo Hipotético":
            "Se P → Q e Q → R são verdadeiras, então P → R também é.",
        "Silogismo Disjuntivo":
            "Se P ∨ Q é verdadeira e uma das alternativas é falsa, a outra é verdadeira.",
        "Dilema Construtivo":
            "Se P → Q e R → S são verdadeiras e P ∨ R é verdadeira, então Q ∨ S é verdadeira.",
        "Falácia: Afirmação do Consequente":
            "Erro: concluir P a partir de P → Q e Q.",
        "Falácia: Negação do Antecedente":
            "Erro: concluir ¬Q a partir de P → Q e ¬P.",
        "Simplificação":
            "De P ∧ Q podemos concluir P ou Q separadamente.",
        "Introdução da Conjunção":
            "De P e Q, concluímos P ∧ Q.",
        "Adição (Introdução da Disjunção)":
            "De P, podemos inferir P ∨ Q.",
        "Exportação":
            "(P ∧ Q) → R é equivalente a P → (Q → R).",
        "Transposição/Contraposição":
            "A contrapositiva de P → Q é ¬Q → ¬P.",
        "Absorção":
            "De P → Q obtemos P → (P ∨ Q), pois se P e Q são verdadeiras, P ∨ Q é verdadeira.",
    }
    return d.get(forma, "Não foi possível gerar uma justificativa automática para esta forma.")

# ---------- MOTOR SIMPLES DE PROVA: MP + MT ----------

def gerar_prova_condicional(premissas_str, conclusao_str):
    """
    Motor de prova simples usando:
    - Modus Ponens
    - Modus Tollens

    Gera linhas de prova enquanto conseguir aplicar
    essas regras. Para quando chegar à conclusão ou
    não houver fórmulas novas.
    """
    premissas = [analisar_formula(p) for p in premissas_str]
    conclusao = analisar_formula(conclusao_str)

    linhas = []
    vistas = set()

    # 1) adicionar premissas
    for i, f in enumerate(premissas, start=1):
        linhas.append({
            "linha": i,
            "formula": f,
            "origem": "Premissa",
            "indices": [],
        })
        vistas.add(str(f))

    proxima_linha = len(linhas) + 1
    mudou = True

    while mudou:
        mudou = False

        # tenta aplicar MP / MT em todos os pares de linhas
        for i in range(len(linhas)):
            for j in range(len(linhas)):
                if i == j:
                    continue

                fi = linhas[i]["formula"]
                fj = linhas[j]["formula"]

                nova_formula = None
                origem_regra = None
                indices = None

                # -------- MODUS PONENS --------
                # fi = A, fj = A -> B
                if isinstance(fj, Implies) and fi == fj.args[0]:
                    nova_formula = fj.args[1]
                    origem_regra = "Modus Ponens"
                    indices = [linhas[i]["linha"], linhas[j]["linha"]]
                # fj = A, fi = A -> B
                elif isinstance(fi, Implies) and fj == fi.args[0]:
                    nova_formula = fi.args[1]
                    origem_regra = "Modus Ponens"
                    indices = [linhas[j]["linha"], linhas[i]["linha"]]

                # -------- MODUS TOLLENS --------
                if nova_formula is None:
                    # fi = ~Q, fj = P -> Q
                    if isinstance(fi, Not) and isinstance(fj, Implies) and fi.args[0] == fj.args[1]:
                        nova_formula = Not(fj.args[0])
                        origem_regra = "Modus Tollens"
                        indices = [linhas[i]["linha"], linhas[j]["linha"]]
                    # fj = ~Q, fi = P -> Q
                    elif isinstance(fj, Not) and isinstance(fi, Implies) and fj.args[0] == fi.args[1]:
                        nova_formula = Not(fi.args[0])
                        origem_regra = "Modus Tollens"
                        indices = [linhas[j]["linha"], linhas[i]["linha"]]

                if nova_formula is None:
                    continue

                if str(nova_formula) in vistas:
                    continue

                linhas.append({
                    "linha": proxima_linha,
                    "formula": nova_formula,
                    "origem": origem_regra,
                    "indices": indices,
                })
                vistas.add(str(nova_formula))
                proxima_linha += 1
                mudou = True

                if nova_formula == conclusao:
                    return linhas

    # não chegou na conclusão: acrescenta linha final “forma não reconhecida”
    if str(conclusao) not in vistas:
        linhas.append({
            "linha": proxima_linha,
            "formula": conclusao,
            "origem": "Forma não reconhecida",
            "indices": list(range(1, len(premissas) + 1)),
        })

    return linhas