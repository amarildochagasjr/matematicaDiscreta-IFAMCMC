import customtkinter as ctk
from PIL import Image, ImageTk
import os
from tkinter import messagebox

prova_atual = None
contexto_atual = None
enunciado_atual = None

# ======== IMPORTA LÓGICA DE PROPOSIÇÕES =========
from proposicao import (
    tabela_verdade,
    classificar_argumento,
    gerar_justificativa,
    aplicar_lei_de_morgan,
    gerar_prova_condicional,
    formatar_formula,
)

# ======== IMPORTA LÓGICA DE PREDICADOS =========
from predicados import (
    verificar_argumento_predicado,  # dominio_str, premissas_str, conclusao_str
    explicar_regra_predicados,
    parse_dominio,
)

# ======== IMPORTA A FUNÇÃO DO LaTeX =========
from exportar_latex import exportar_prova_latex

premissas_entries = []
conclusao_entry = None
saida_text = None
qtd_premissas_menu = None


dominio_entry = None
premissas_pred_entries = []  # várias premissas
conclusao_pred_entry = None
qtd_premissas_pred_menu = None

def atualizar_premissas(qtd_str: str):
    global premissas_entries
    qtd = int(qtd_str)

    for entry in premissas_entries:
        entry.grid_forget()
    premissas_entries.clear()

    for i in range(qtd):
        entry = ctk.CTkEntry(
            janela_principal,
            width=300,
            placeholder_text=f"Premissa {i+1} (ex: P -> Q)",
        )
        entry.grid(row=3 + i, column=0, padx=15, sticky="w")
        premissas_entries.append(entry)

def atualizar_premissas_pred(qtd_str: str):
    global premissas_pred_entries
    qtd = int(qtd_str)

    for entry in premissas_pred_entries:
        entry.grid_forget()
    premissas_pred_entries.clear()

    for i in range(qtd):
        entry = ctk.CTkEntry(
            janela_principal,
            width=300,
            placeholder_text=f"Premissa {i + 1} (ex: (Ax)P(x))",
        )

        entry.grid(row=5 + i, column=0, padx=15, pady=(10,0),sticky="w")
        premissas_pred_entries.append(entry)

def validar_premissas():
    global prova_atual, contexto_atual, enunciado_atual
    contexto_atual = "PROPOSICOES"
    prova_atual = None
    enunciado_atual = None

    premissas = [e.get().strip() for e in premissas_entries if e.get().strip() != ""]
    conclusao = conclusao_entry.get().strip()

    if not premissas or not conclusao:
        saida_text.delete("1.0", "end")
        saida_text.insert("end", "Preencha todas as premissas e a conclusão.\n")
        botao_exportar_latex.configure(state="disabled")
        return

    try:
        (
            variaveis,
            tabela,
            argumento_valido,
            premissas_simbolicas,
            conclusao_simbolica,
        ) = tabela_verdade(premissas, conclusao)
        forma = classificar_argumento(premissas, conclusao)
        justif = gerar_justificativa(forma)

        saida_text.delete("1.0", "end")
        saida_text.insert("end", f"Forma identificada: {forma}\n")
        saida_text.insert(
            "end",
            f"Argumento válido? {'SIM' if argumento_valido else 'NÃO'}\n",
        )
        saida_text.insert("end", f"Justificativa: {justif}\n\n")

        # ----- TABELA-VERDADE (alinhada) -----
        cabecalho = (
                [v.name for v in variaveis]
                + [formatar_formula(p) for p in premissas_simbolicas]
                + [formatar_formula(conclusao_simbolica)]
        )

        largura_col = max(5, max(len(col) for col in cabecalho))

        def fmt_cab(col):
            return col.center(largura_col)

        def fmt_val(x):
            return ("V" if x else "F").center(largura_col)

        linha_cab = " | ".join(fmt_cab(col) for col in cabecalho)
        saida_text.insert("end", linha_cab + "\n")
        saida_text.insert("end", "-" * len(linha_cab) + "\n")

        for ambiente, valores_premissas, valor_conclusao in tabela:
            valores = [ambiente[v] for v in variaveis] + valores_premissas + [
                valor_conclusao
            ]
            linha = " | ".join(fmt_val(x) for x in valores)
            saida_text.insert("end", linha + "\n\n")

        prova_atual = None
        if forma.startswith("Falácia"):
            saida_text.insert(
                "end",
                "Árvore de prova não exibida para formas falaciosas.\n",
            )
            botao_exportar_latex.configure(state="disabled")
        else:
            saida_text.insert("end", "Árvore de Prova:\n")

            linhas_prova = gerar_prova_condicional(premissas, conclusao)

            prova_atual = []

            for linha in linhas_prova:
                num = linha["linha"]
                formula_str = formatar_formula(linha["formula"])
                origem = linha["origem"]
                indices = linha["indices"]

                if indices:
                    idx_txt = ", ".join(str(i) for i in indices)
                    justif_linha = f"{origem}: {idx_txt}"
                else:
                    justif_linha = origem

                saida_text.insert("end", f"{num}. {formula_str}    [{justif_linha}]\n")
                prova_atual.append((num, formula_str, justif_linha))

            if formatar_formula(linhas_prova[-1]["formula"]) == formatar_formula(
                conclusao_simbolica
            ):
                saida_text.insert("end", "✓ Q.E.D.\n")

            enunciado_atual = (
                f"Premissas: {', '.join(premissas)}  Conclusão: {conclusao}"
            )
            botao_exportar_latex.configure(state="normal")

    except Exception as e:
        saida_text.delete("1.0", "end")
        saida_text.insert("end", f"Erro ao processar: {e}\n")
        prova_atual = None
        enunciado_atual = None
        botao_exportar_latex.configure(state="disabled")

def aplicar_leis_de_morgan():
    saida_text.delete("1.0", "end")
    for idx, entry in enumerate(premissas_entries, start=1):
        texto = entry.get().strip()
        if not texto:
            continue

        equivalente, nome_lei = aplicar_lei_de_morgan(texto)

        if nome_lei is None:
            saida_text.insert(
                "end",
                f"Premissa {idx}: nenhuma Lei de De Morgan se aplica.\n",
            )
        else:
            saida_text.insert(
                "end",
                f"Premissa {idx}: {nome_lei}\n"
                f"  Original: {texto}\n"
                f"  Equivalente: {formatar_formula(equivalente)}\n\n",
            )

def verificar_predicado():
    global prova_atual, contexto_atual, enunciado_atual
    contexto_atual = "PREDICADOS"
    prova_atual = None
    enunciado_atual = None

    dominio_str = dominio_entry.get().strip()
    premissas = [e.get().strip() for e in premissas_pred_entries if e.get().strip()]
    conclusao_str = conclusao_pred_entry.get().strip()

    if not dominio_str or not premissas or not conclusao_str:
        saida_text.delete("1.0", "end")
        saida_text.insert("end", "Preencha domínio, premissas e conclusão.\n")
        botao_exportar_latex.configure(state="disabled")
        return

    if len(premissas) == 1:
        p_sem_espaco = premissas[0].replace(" ", "")
        c_sem_espaco = conclusao_str.replace(" ", "")
        if p_sem_espaco == "~(Ax)P(x)" and c_sem_espaco in ["(Ex)~P(x)", "(existsx)~P(x)"]:
            saida_text.delete("1.0", "end")
            dom = parse_dominio(dominio_str)
            saida_text.insert("end", f"Domínio: {dom}\n")
            saida_text.insert("end", "Argumento válido? SIM\n")
            saida_text.insert(
                "end",
                "Método: Equivalência conhecida (De Morgan em quantificadores).\n",
            )
            saida_text.insert(
                "end",
                "Regra aplicada: ~ (∀x)P(x) é logicamente equivalente a (∃x)~P(x).\n",
            )
            enunciado_atual = (
                f"Domínio: {dom}  Premissas: {premissas[0]}  Conclusão: {conclusao_str}"
            )
            prova_atual = []
            botao_exportar_latex.configure(state="normal")
            return

    try:
        valido, contraexemplos, dominio, nomes_pred = verificar_argumento_predicado(
            dominio_str, premissas, conclusao_str
        )

        saida_text.delete("1.0", "end")
        saida_text.insert("end", f"Domínio: {dominio}\n")
        saida_text.insert("end", f"Predicados unários: {nomes_pred}\n")
        saida_text.insert(
            "end",
            f"Argumento válido? {'SIM' if valido else 'NÃO'}\n",
        )

        saida_text.insert("end", "Método: Enumeração em domínio finito.\n")
        regra = explicar_regra_predicados(premissas, conclusao_str)
        saida_text.insert("end", f"Regra aplicada: {regra}\n\n")

        if not valido and contraexemplos:
            saida_text.insert("end", "Contraexemplo (uma interpretação):\n")
            interp = contraexemplos[0]
            for nome in nomes_pred:
                saida_text.insert(
                    "end",
                    f"{nome} verdadeiro em: {sorted(list(interp.get(nome, [])))}\n",
                )

        enunciado_atual = (
            f"Domínio: {dominio}  Premissas: {', '.join(premissas)}  Conclusão: {conclusao_str}"
        )
        prova_atual = []
        botao_exportar_latex.configure(state="normal")

    except Exception as e:
        saida_text.delete("1.0", "end")
        saida_text.insert("end", f"Erro ao processar predicados: {e}\n")
        prova_atual = None
        enunciado_atual = None
        botao_exportar_latex.configure(state="disabled")

def exportar_latex_callback():
    if not prova_atual:
        messagebox.showwarning(
            "Exportar", "Nenhuma prova disponível para exportar."
        )
        return

    try:
        base_dir = os.path.dirname(__file__)
        caminho = os.path.join(base_dir, "prova_atual.tex")
        exportar_prova_latex(prova_atual, caminho=caminho, titulo="Prova do argumento")
        messagebox.showinfo("Exportar", f"Arquivo gerado: {caminho}")
    except Exception as e:
        messagebox.showerror("Exportar", f"Falha ao exportar: {e}")

def mostrar_widgets_proposicoes():
    label_premissas.grid(
        row=2, column=0, padx=(15, 0), pady=(100, 5), sticky="w"
    )
    qtd_premissas_menu.grid(
        row=2, column=0, padx=(210, 0), pady=(100, 5), sticky="w"
    )
    atualizar_premissas("1")

    conclusao_label.grid(
        row=8, column=0, padx=15, pady=(10, 0), sticky="w"
    )
    conclusao_entry.grid(row=9, column=0, padx=15, sticky="w")
    botao_verificar.grid(
        row=10, column=0, padx=15, pady=(10, 0), sticky="w"
    )
    botao_morgan.grid(
        row=10, column=0, padx=200, pady=(10, 0), sticky="w"
    )
    botao_exportar_latex.grid(
        row=10, column=0, padx=400, pady=(10, 0), sticky="w"
    )
    botao_exportar_latex.configure(state="disabled")

def esconder_widgets_proposicoes():
    label_premissas.grid_forget()
    qtd_premissas_menu.grid_forget()
    for e in premissas_entries:
        e.grid_forget()
    conclusao_label.grid_forget()
    conclusao_entry.grid_forget()
    botao_verificar.grid_forget()
    botao_morgan.grid_forget()
    botao_exportar_latex.grid_forget()

def mostrar_widgets_predicados():
    dominio_label.grid(row=3, column=0, padx=15, pady=(10, 0), sticky="w")
    dominio_entry.grid(row=3, column=0, padx=165,pady=(11, 0), sticky="w")

    premissa_pred_label.grid(row=4, column=0, padx=15, pady=(10, 0), sticky="w")

    qtd_premissas_pred_menu.grid(
        row=4, column=0, padx=(200, 0), pady=(10, 0), sticky="w"
    )
    qtd_premissas_pred_menu.set("1")
    atualizar_premissas_pred("1")  # cria Premissa 1 em row=6

    conclusao_pred_label.grid(row=8, column=0, padx=15, pady=(10, 0), sticky="w")
    conclusao_pred_entry.grid(row=9, column=0, padx=15, sticky="w")

    botao_verificar_pred.grid(
        row=10, column=0, padx=15, pady=(10, 0), sticky="w"
    )

    glossario_label.grid(row=6, column=0, padx=350, pady=(10, 0), sticky="w")

    '''botao_exportar_latex.grid(
        row=10, column=0, padx=180, pady=(10, 0), sticky="w"
    )
    botao_exportar_latex.configure(state="disabled")''' #comentei porque não deu certo, não ta exportando para predicados

def esconder_widgets_predicados():
    dominio_label.grid_forget()
    dominio_entry.grid_forget()
    qtd_premissas_pred_menu.grid_forget()
    premissa_pred_label.grid_forget()
    for e in premissas_pred_entries:
        e.grid_forget()
    conclusao_pred_label.grid_forget()
    conclusao_pred_entry.grid_forget()
    botao_verificar_pred.grid_forget()
    glossario_label.grid_forget()
    #botao_exportar_latex.grid_forget() #comentei porque não deu certo, não ta exportando para predicados

def escolha_callback(valor: str):
    numero = int(valor.split(".")[0])
    saida_text.delete("1.0", "end")

    global prova_atual, enunciado_atual, contexto_atual
    prova_atual = None
    enunciado_atual = None
    contexto_atual = None
    botao_exportar_latex.configure(state="disabled")

    if numero == 1:
        esconder_widgets_predicados()
        mostrar_widgets_proposicoes()
    elif numero == 2:
        esconder_widgets_proposicoes()
        mostrar_widgets_predicados()

    label_valor.configure(text=valor)

ctk.set_appearance_mode("dark")

janela_principal = ctk.CTk()
janela_principal.title("IMPLEMENTAÇÃO MATEMÁTICA DISCRETA")
janela_principal.geometry("1000x700")
janela_principal.resizable(True, True)

base_dir = os.path.dirname(__file__)
icon_path = os.path.join(base_dir, "assets", "ifamlogo.png")
if os.path.exists(icon_path):
    icon_image = Image.open(icon_path)
    app_icon = ImageTk.PhotoImage(icon_image)
    janela_principal.icon_ref = app_icon
    janela_principal.wm_iconphoto(False, app_icon)

janela_principal.grid_rowconfigure(11, weight=1)
janela_principal.grid_columnconfigure(0, weight=1)

cabecalho = ctk.CTkLabel(
    janela_principal,
    text="MATEMÁTICA DISCRETA",
    font=("Arial", 25, "bold"),
)
cabecalho.grid(row=0, column=0, pady=(20, 0), sticky="n")

mensagem = ctk.CTkLabel(
    janela_principal,
    text="Escolha uma das opções abaixo:",
    font=("Arial", 17, "bold"),
)
mensagem.grid(row=1, column=0, pady=(10, 0), sticky="n")

label_valor = ctk.CTkLabel(
    janela_principal,
    text="",
    font=("Arial", 15, "bold"),
)
label_valor.grid(row=2, column=0, pady=(50, 0), sticky="n")

escolha_menu = ctk.CTkOptionMenu(
    janela_principal,
    values=["1. PROPOSIÇÕES", "2. PREDICADOS"],
    width=175,
    corner_radius=27,
    fg_color="#2F9E41",
    button_color="#DC0000",
    command=escolha_callback,
)
escolha_menu.grid(row=2, column=0, pady=(20, 0), sticky="n")
escolha_menu.set(" --- Escolha ---")

label_premissas = ctk.CTkLabel(
    janela_principal,
    text="Quantidade de premissas:",
    font=("Arial", 15, "bold"),
)

qtd_premissas_menu = ctk.CTkOptionMenu(
    janela_principal,
    values=[str(i) for i in range(1, 6)],
    command=atualizar_premissas,
    width=75,
    corner_radius=27,
)

dominio_label = ctk.CTkLabel(
    janela_principal,
    text="Domínio (ex: {1,2,3}):",
    font=("Arial", 15, "bold"),
)

dominio_entry = ctk.CTkEntry(
    janela_principal,
    width=100,
    placeholder_text="{1,2,3}",
)

qtd_premissas_pred_menu = ctk.CTkOptionMenu(
    janela_principal,
    values=[str(i) for i in range(1, 4)],
    command=atualizar_premissas_pred,
    width=75,
    corner_radius=27,
)

premissa_pred_label = ctk.CTkLabel(
    janela_principal,
    text="Premissas de predicados:",
    font=("Arial", 15, "bold"),
)

conclusao_pred_label = ctk.CTkLabel(
    janela_principal,
    text="Conclusão (ex: (∃x)P(x)):",
    font=("Arial", 15, "bold"),
)

conclusao_pred_entry = ctk.CTkEntry(
    janela_principal,
    width=300,
    placeholder_text="(∃x)P(x)",
)

botao_verificar_pred = ctk.CTkButton(
    janela_principal,
    text="Verificar predicado",
    command=verificar_predicado,
)

conclusao_label = ctk.CTkLabel(
    janela_principal,
    text="Conclusão:",
    font=("Arial", 15, "bold"),
)

conclusao_entry = ctk.CTkEntry(
    janela_principal,
    width=300,
    placeholder_text="Conclusão (ex: R)",
)

botao_verificar = ctk.CTkButton(
    janela_principal,
    text="Verificar argumento",
    command=validar_premissas,
)

botao_morgan = ctk.CTkButton(
    janela_principal,
    text="Aplicar Leis de De Morgan",
    command=aplicar_leis_de_morgan,
)

botao_exportar_latex = ctk.CTkButton(
    janela_principal,
    text="Exportar LaTeX",
    command=exportar_latex_callback,
)

saida_text = ctk.CTkTextbox(
    janela_principal,
    width=600,
    height=200,
)
saida_text.grid(
    row=11, column=0, padx=15, pady=(10, 15), sticky="nsew"
)

glossario_label = ctk.CTkLabel(
    janela_principal,
    text="∀: digite (Ax) ou (forallx)\n"
    "∃: digite (Ex) ou (existsx)",
    font=("Arial", 15),
    justify="left",
)

janela_principal.mainloop()
