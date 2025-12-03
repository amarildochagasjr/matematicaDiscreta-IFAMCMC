from pyparsing import (
    Word, alphas, alphanums, oneOf, infixNotation,
    opAssoc, ParserElement, Literal, Group, Forward
)
import itertools

ParserElement.enablePackrat()

# ---------------- DOMÍNIO ----------------

def parse_dominio(dominio_str: str):
    """
    Exemplo de entrada: {1, 2, 3} ou {a, b, c}
    Retorna lista de constantes como strings: ["1","2","3"].
    """
    s = dominio_str.strip()
    if s.startswith("{") and s.endswith("}"):
        s = s[1:-1]
    if not s:
        return []
    partes = [p.strip() for p in s.split(",")]
    return [p for p in partes if p]

# ---------------- AST PARA PREDICADOS ----------------

class Predicado:
    def __init__(self, nome, args):
        self.nome = nome
        self.args = args

    def __repr__(self):
        args_str = ", ".join(self.args)
        return f"{self.nome}({args_str})"

class ForAll:
    def __init__(self, var, subf):
        self.var = var
        self.subf = subf

    def __repr__(self):
        return f"(∀{self.var}){self.subf}"

class Exists:
    def __init__(self, var, subf):
        self.var = var
        self.subf = subf

    def __repr__(self):
        return f"(∃{self.var}){self.subf}"

class Not:
    def __init__(self, subf):
        self.subf = subf

    def __repr__(self):
        return f"~{self.subf}"

class BinOp:
    def __init__(self, op, left, right):
        self.op = op  # "&", "v", "->"
        self.left = left
        self.right = right

    def __repr__(self):
        return f"({self.left} {self.op} {self.right})"

# ---------------- PARSER ----------------

def criar_parser_predicados():
    var = Word(alphas.lower(), exact=1)
    const = Word(alphanums, min=1)
    nome_pred = Word(alphas.upper(), exact=1)

    lpar = Literal("(").suppress()
    rpar = Literal(")").suppress()
    virg = Literal(",").suppress()

    termo = (var | const).setParseAction(lambda t: t[0])

    def predicado_action(tokens):
        nome = tokens[0]
        args = tokens[1:]
        return Predicado(nome, args)

    predicado = (nome_pred + lpar + termo + Group((virg + termo)[...]) + rpar)
    predicado.setParseAction(lambda t: predicado_action([t[0]] + [t[1]] + list(t[2])))

    forall = (Literal("(A") | Literal("(forall")) + var + Literal(")")
    exists = (Literal("(E") | Literal("(exists")) + var + Literal(")")

    NOT = oneOf("~ ¬")
    AND = oneOf("& ∧")
    OR  = oneOf("v V |")
    IMP = Literal("->")

    def quant_forall_action(tokens):
        varname = tokens[1]
        def wrap(subtree):
            return ForAll(varname, subtree)
        return wrap

    def quant_exists_action(tokens):
        varname = tokens[1]
        def wrap(subtree):
            return Exists(varname, subtree)
        return wrap

    def not_action(tokens):
        return Not(tokens[0][1])

    def binop_action(op):
        def act(tokens):
            t = tokens[0]
            left = t[0]
            for i in range(2, len(t), 2):
                right = t[i]
                left = BinOp(op, left, right)
            return left
        return act

    def apply_quantifier(tokens):
        wrap = tokens[0][0]
        subf = tokens[0][1]
        return wrap(subf)

    expr = Forward()
    atom = predicado | (lpar + expr + rpar)

    expr <<= infixNotation(
        atom,
        [
            (forall.setParseAction(quant_forall_action), 1, opAssoc.RIGHT, apply_quantifier),
            (exists.setParseAction(quant_exists_action), 1, opAssoc.RIGHT, apply_quantifier),
            (NOT,   1, opAssoc.RIGHT, not_action),
            (AND,   2, opAssoc.LEFT,  binop_action("&")),
            (OR,    2, opAssoc.LEFT,  binop_action("v")),
            (IMP,   2, opAssoc.RIGHT, binop_action("->")),
        ]
    )

    return expr


# ---------------- AVALIAÇÃO EM DOMÍNIO FINITO ----------------

def avaliar_predicado(pred: Predicado, interpretacao, ambiente):
    nome = pred.nome
    args = []
    for arg in pred.args:
        if arg in ambiente:
            args.append(ambiente[arg])
        else:
            args.append(arg)
    if len(args) == 1:
        d = args[0]
        verdadeiros = interpretacao.get(nome, set())
        return d in verdadeiros
    else:
        raise ValueError("Somente predicados unários são suportados por enquanto.")

def avaliar_formula(formula, dominio, interpretacao, ambiente):
    if isinstance(formula, Predicado):
        return avaliar_predicado(formula, dominio, interpretacao, ambiente)

    if isinstance(formula, Not):
        return not avaliar_formula(formula.subf, dominio, interpretacao, ambiente)

    if isinstance(formula, BinOp):
        left = avaliar_formula(formula.left, dominio, interpretacao, ambiente)
        right = avaliar_formula(formula.right, dominio, interpretacao, ambiente)
        if formula.op == "&":
            return left and right
        if formula.op == "v":
            return left or right
        if formula.op == "->":
            return (not left) or right
        raise ValueError(f"Operador desconhecido: {formula.op}")

    if isinstance(formula, ForAll):
        var = formula.var
        for d in dominio:
            ambiente[var] = d
            if not avaliar_formula(formula.subf, dominio, interpretacao, ambiente):
                return False
        return True

    if isinstance(formula, Exists):
        var = formula.var
        for d in dominio:
            ambiente[var] = d
            if avaliar_formula(formula.subf, dominio, interpretacao, ambiente):
                return True
        return False

    raise ValueError(f"Tipo de fórmula desconhecido: {formula}")

# ---------------- ENUMERAÇÃO DE INTERPRETAÇÕES ----------------

def coletar_predicados_unarios(formulas):
    nomes = set()

    def visita(f):
        if isinstance(f, Predicado):
            if len(f.args) == 1:
                nomes.add(f.nome)
        elif isinstance(f, Not):
            visita(f.subf)
        elif isinstance(f, BinOp):
            visita(f.left)
            visita(f.right)
        elif isinstance(f, ForAll) or isinstance(f, Exists):
            visita(f.subf)

    for f in formulas:
        visita(f)
    return sorted(nomes)

def gerar_interpretacoes(dominio, nomes_pred_unarios):
    """
    Para cada predicado P, interpretação é subconjunto de domínio.
    Gera todas as combinações possíveis (cartesiano).
    """
    dominio_set = list(dominio)
    todas_interps = []

    subconjuntos = []
    for _ in nomes_pred_unarios:
        pred_subs = []
        for mask in range(1 << len(dominio_set)):
            subs = {dominio_set[i] for i in range(len(dominio_set)) if (mask & (1 << i))}
            pred_subs.append(subs)
        subconjuntos.append(pred_subs)

    for escolha in itertools.product(*subconjuntos):
        interp = {}
        for nome, conj in zip(nomes_pred_unarios, escolha):
            interp[nome] = conj
        todas_interps.append(interp)

    return todas_interps

# ---------------- VERIFICADOR DE ARGUMENTO ----------------

def verificar_argumento_predicado(dominio_str, premissas_str, conclusao_str):
    """
    dominio_str: ex: "{1,2,3}"
    premissas_str: lista de strings, ex: ["(∀x)P(x)"]
    conclusao_str: string, ex: "(∃x)P(x)"

    Retorna:
    - valido (bool)
    - contraexemplos (lista de interpretações onde premissas são V e conclusão é F)
    """
    dominio = parse_dominio(dominio_str)
    premissas = [parse_formula_predicado(p) for p in premissas_str]
    conclusao = parse_formula_predicado(conclusao_str)

    formulas = premissas + [conclusao]
    nomes_pred = coletar_predicados_unarios(formulas)
    interps = gerar_interpretacoes(dominio, nomes_pred)

    contraexemplos = []

    for interp in interps:
        ambiente = {}
        todas_premissas_v = True
        for p in premissas:
            if not avaliar_formula(p, dominio, interp, ambiente.copy()):
                todas_premissas_v = False
                break

        if not todas_premissas_v:
            continue

        if not avaliar_formula(conclusao, dominio, interp, ambiente.copy()):
            contraexemplos.append(interp)

    valido = len(contraexemplos) == 0
    return valido, contraexemplos, dominio, nomes_pred

_parser_pred = criar_parser_predicados()

def parse_formula_predicado(s: str):
    """
    Faz o parse de uma fórmula de predicados dada como string
    e devolve a AST correspondente (Predicado, ForAll, Exists, etc.).
    """
    return _parser_pred.parseString(s.strip(), parseAll=True)[0]

def explicar_regra_predicados(premissas_str, conclusao_str):
    c = conclusao_str.replace(" ", "")

    # ------------ CASO: DUAS PREMISSAS (Silogismo de Aristóteles) ------------
    if len(premissas_str) == 2:
        p1 = premissas_str[0].replace(" ", "")
        p2 = premissas_str[1].replace(" ", "")

        # Silogismo de Aristóteles:
        # (Ax)(H(x)->M(x)), H(1) |- M(1)
        if (p1.startswith("(Ax)(") or p1.startswith("(forallx)(")) \
           and "H(x)->M(x)" in p1 \
           and p2.startswith("H(") and c.startswith("M(") \
           and p2[2:-1] == c[2:-1]:
            return "Silogismo de Aristóteles: de (∀x)(H(x)→M(x)) e H(c) concluímos M(c)."

    # ------------ CASO: UMA PREMISSA ------------
    if len(premissas_str) == 1:
        p = premissas_str[0].replace(" ", "")

        # Particularização universal:
        # (Ax)P(x) |- P(1)
        if (p.startswith("(Ax)") or p.startswith("(forallx)")) \
           and p.endswith("P(x)") \
           and c.startswith("P(") and c.endswith(")"):
            return "Particularização universal: de (∀x)P(x) concluímos P(c) para um elemento específico c."

        # Generalização universal:
        # P(1) |- (Ax)P(x)
        if c.startswith("(Ax)") or c.startswith("(forallx)"):
            corpo = None
            if c.startswith("(Ax)"):
                corpo = c[len("(Ax)"):]
            elif c.startswith("(forallx)"):
                corpo = c[len("(forallx)"):]
            if corpo is not None:
                corpo = corpo.replace(" ", "")
                if corpo == "P(x)" and p.startswith("P(") and p.endswith(")"):
                    return "Generalização universal: de P(c) concluímos (∀x)P(x), assumindo que c foi escolhido arbitrariamente."

        # Particularização existencial:
        # (Ex)P(x) |- P(1)
        if (p.startswith("(Ex)") or p.startswith("(existsx)")) \
           and p.endswith("P(x)") \
           and c.startswith("P(") and c.endswith(")"):
            return "Particularização existencial: de (∃x)P(x) concluímos P(c) para algum elemento específico c."

        # Generalização existencial:
        # P(1) |- (Ex)P(x)
        if c.startswith("(Ex)") or c.startswith("(existsx)"):
            corpo = None
            if c.startswith("(Ex)"):
                corpo = c[len("(Ex)"):]
            elif c.startswith("(existsx)"):
                corpo = c[len("(existsx)"):]
            if corpo is not None:
                corpo = corpo.replace(" ", "")
                if corpo == "P(x)" and p.startswith("P(") and p.endswith(")"):
                    return "Generalização existencial: de P(c) concluímos (∃x)P(x)."

    return "Não foi possível identificar automaticamente uma regra de quantificadores."