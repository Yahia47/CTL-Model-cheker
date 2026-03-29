# -*- coding: utf-8 -*-
import sys, io
sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8', errors='replace')
sys.stderr = io.TextIOWrapper(sys.stderr.buffer, encoding='utf-8', errors='replace')

# ================================================================
#   CTL MODEL CHECKER - Console Simple + Graphe ASCII
# ================================================================

import re

# ================================================================
# PARTIE 1 - Classes
# ================================================================

class State:
    def __init__(self, name, propositions=None):
        self.name         = name
        self.propositions = set(propositions) if propositions else set()
        self.transitions  = []

    def add_transition(self, state):
        if state not in self.transitions:
            self.transitions.append(state)


# ================================================================
# PARTIE 2 - Formules CTL
# ================================================================

class CTLFormula: pass
class Atom(CTLFormula):
    def __init__(self, n): self.name = n
    def __repr__(self): return self.name
class Not(CTLFormula):
    def __init__(self, f): self.formula = f
    def __repr__(self): return f"!({self.formula})"
class And(CTLFormula):
    def __init__(self, l, r): self.left=l; self.right=r
    def __repr__(self): return f"({self.left} && {self.right})"
class Or(CTLFormula):
    def __init__(self, l, r): self.left=l; self.right=r
    def __repr__(self): return f"({self.left} || {self.right})"
class EX(CTLFormula):
    def __init__(self, f): self.formula=f
    def __repr__(self): return f"Eo({self.formula})"
class AX(CTLFormula):
    def __init__(self, f): self.formula=f
    def __repr__(self): return f"Ao({self.formula})"
class EF(CTLFormula):
    def __init__(self, f): self.formula=f
    def __repr__(self): return f"E<>({self.formula})"
class AF(CTLFormula):
    def __init__(self, f): self.formula=f
    def __repr__(self): return f"A<>({self.formula})"
class EG(CTLFormula):
    def __init__(self, f): self.formula=f
    def __repr__(self): return f"E[]({self.formula})"
class AG(CTLFormula):
    def __init__(self, f): self.formula=f
    def __repr__(self): return f"A[]({self.formula})"
class EU(CTLFormula):
    def __init__(self, l, r): self.left=l; self.right=r
    def __repr__(self): return f"E[{self.left} U {self.right}]"
class AU(CTLFormula):
    def __init__(self, l, r): self.left=l; self.right=r
    def __repr__(self): return f"A[{self.left} U {self.right}]"


# ================================================================
# PARTIE 3 - Model Checker
# ================================================================

class CTLModelChecker:
    def __init__(self, states): self.states = states

    def check(self, formula, state):
        if isinstance(formula, Atom):  return formula.name in state.propositions
        if isinstance(formula, Not):   return not self.check(formula.formula, state)
        if isinstance(formula, And):   return self.check(formula.left,state) and self.check(formula.right,state)
        if isinstance(formula, Or):    return self.check(formula.left,state) or  self.check(formula.right,state)
        if isinstance(formula, EX):    return any(self.check(formula.formula,s) for s in state.transitions)
        if isinstance(formula, AX):
            if not state.transitions: return True
            return all(self.check(formula.formula,s) for s in state.transitions)
        if isinstance(formula, EF):    return self._ef(formula.formula, state, set())
        if isinstance(formula, AF):    return self._af(formula.formula, state, set())
        if isinstance(formula, EG):    return self._eg(formula.formula, state, set())
        if isinstance(formula, AG):    return self._ag(formula.formula, state, set())
        if isinstance(formula, EU):    return self._eu(formula.left,   formula.right, state, set())
        if isinstance(formula, AU):    return self._au(formula.left,   formula.right, state, set())
        raise ValueError(f"Formule inconnue")

    def check_all(self, formula, states_dict):
        # Chaque état a son propre visited séparé !
        return {nom: self.check(formula, s) for nom, s in states_dict.items()}

    def _ef(self, f, s, visited):
        if self.check(f, s): return True
        if s.name in visited: return False
        visited.add(s.name)
        return any(self._ef(f, n, visited) for n in s.transitions)

    def _af(self, f, s, visited):
        if self.check(f, s): return True
        if s.name in visited: return False
        visited.add(s.name)
        if not s.transitions: return False
        return all(self._af(f, n, visited) for n in s.transitions)

    def _eg(self, f, s, visited):
        if not self.check(f, s): return False
        if s.name in visited: return True
        visited.add(s.name)
        if not s.transitions: return True
        return any(self._eg(f, n, visited) for n in s.transitions)

    def _ag(self, f, s, visited):
        if not self.check(f, s): return False
        if s.name in visited: return True
        visited.add(s.name)
        return all(self._ag(f, n, visited) for n in s.transitions)

    def _eu(self, l, r, s, visited):
        if self.check(r, s): return True
        if not self.check(l, s): return False
        if s.name in visited: return False
        visited.add(s.name)
        return any(self._eu(l, r, n, visited) for n in s.transitions)

    def _au(self, l, r, s, visited):
        if self.check(r, s): return True
        if not self.check(l, s): return False
        if s.name in visited: return False
        visited.add(s.name)
        if not s.transitions: return False
        return all(self._au(l, r, n, visited) for n in s.transitions)


# ================================================================
# PARTIE 4 - Parser (remozes simples)
# ================================================================

def normaliser(text):
    """
    Converts Tina-style symbols to standard CTL internal format.

    Tina  ->  Internal
    Eop   ->  EX(p)      Next exists
    Aop   ->  AX(p)      Next forall
    E<>p  ->  EF(p)      Futur exists
    A<>p  ->  AF(p)      Futur forall
    E[]p  ->  EG(p)      Always exists
    A[]p  ->  AG(p)      Always forall
    E[pUq]->  EU(p,q)    Until exists
    A[pUq]->  AU(p,q)    Until forall
    !p    ->  NOT(p)
    p&&q  ->  AND inline
    p||q  ->  OR inline
    """
    t = text.strip()

    # -- Step 1: Until  E[p U q]  A[p U q]
    def rep_u(m):
        quant = m.group(1).upper()
        op    = 'EU' if quant == 'E' else 'AU'
        return f"{op}({m.group(2).strip()},{m.group(3).strip()})"
    t = re.sub(r'([EeAa])\[(.+?)\s+[Uu]\s+(.+?)\]', rep_u, t)
    t = re.sub(r'([EeAa])\[(.+?)[Uu](.+?)\]',       rep_u, t)

    # -- Step 2: Replace Tina operators with standard names
    # Order matters: replace E<> before E[], replace longer tokens first
    # We replace the operator token only, keeping what follows intact
    replacements = [
        (r'[Ee]<>',   'EF'),
        (r'[Aa]<>',   'AF'),
        (r'[Ee]\[\]', 'EG'),
        (r'[Aa]\[\]', 'AG'),
        (r'[Ee]o',    'EX'),
        (r'[Aa]o',    'AX'),
    ]
    for pat, repl in replacements:
        # Replace token when followed by ( or a word char
        t = re.sub(pat + r'(?=\(|\w)', repl, t)

    # -- Step 3: EF p  ->  EF(p)  - add parens when operator followed by bare word
    # After step 2 we may have: EFp  EGq  EXa  etc.
    for op in ['EF','AF','EG','AG','EX','AX']:
        # op followed by a bare identifier (no paren already)
        t = re.sub(r'\b' + op + r'(?!\()(\w+)', lambda m, o=op: f"{o}({m.group(1)})", t)

    # -- Step 4: !p  /  !(...)  ->  NOT(...)
    t = re.sub(r'!\((.+?)\)', lambda m: f"NOT({m.group(1)})", t)
    t = re.sub(r'!(\w+)',     lambda m: f"NOT({m.group(1)})", t)

    # -- Step 5: Uppercase CTL keywords (handles lowercase input)
    for op in ["EU","AU","EX","AX","EF","AF","EG","AG","NOT","AND","OR"]:
        t = re.sub(r'(?i)\b' + op + r'\b', op, t)

    return t

def split_args(text):
    depth = 0
    for i, ch in enumerate(text):
        if ch == '(':   depth += 1
        elif ch == ')': depth -= 1
        elif ch == ',' and depth == 0:
            return text[:i].strip(), text[i+1:].strip()
    return None, None

def parse_formula(text):
    text = normaliser(text.strip())
    # && / ||
    depth = 0
    for i, ch in enumerate(text):
        if ch == '(':   depth += 1
        elif ch == ')': depth -= 1
        elif depth == 0:
            if text[i:i+2] == '&&': return And(parse_formula(text[:i]),  parse_formula(text[i+2:]))
            if text[i:i+2] == '||': return Or( parse_formula(text[:i]),  parse_formula(text[i+2:]))
    for op in ["EU","AU","AND","OR"]:
        if text.startswith(op+"(") and text.endswith(")"):
            l, r = split_args(text[len(op)+1:-1])
            if l is None: continue
            f1 = parse_formula(l); f2 = parse_formula(r)
            if op=="EU": return EU(f1,f2)
            if op=="AU": return AU(f1,f2)
            if op=="AND": return And(f1,f2)
            if op=="OR":  return Or(f1,f2)
    for op, cls in [("NOT",Not),("EX",EX),("AX",AX),
                    ("EF",EF),("AF",AF),("EG",EG),("AG",AG)]:
        if text.startswith(op+"(") and text.endswith(")"):
            return cls(parse_formula(text[len(op)+1:-1]))
    if re.match(r'^[A-Za-z_]\w*$', text):
        return Atom(text)
    raise ValueError(f"Formule non reconnue : '{text}'")


# ================================================================
# PARTIE 5 - Dessin du graphe ASCII automatique
# ================================================================

def dessiner_graphe(states_dict):
    """
    Dessine un graphe ASCII simple et propre.
    Les états sont affichés en ligne avec leurs propositions,
    et les flèches de transition sont affichées en dessous.
    """
    noms   = list(states_dict.keys())
    n      = len(noms)
    W      = 12   # largeur de chaque boîte

    print()
    print("  +" + "="*62 + "+")
    print("  |" + "       GRAPHE DU SYSTÈME DE TRANSITIONS".center(62) + "|")
    print("  +" + "="*62 + "+")
    print()

    # -- Ligne des boîtes d'états -----------------------------
    # Affichage par rangées de max 5 états
    rangee_max = 5
    rangees    = [noms[i:i+rangee_max] for i in range(0, n, rangee_max)]

    for rangee in rangees:
        # Ligne du haut des boîtes
        ligne_top  = "  "
        ligne_nom  = "  "
        ligne_prop = "  "
        ligne_bot  = "  "

        for nom in rangee:
            state = states_dict[nom]
            props = ",".join(sorted(state.propositions)) if state.propositions else "{}"
            # boîte de largeur W
            w     = max(W, len(nom)+4, len(props)+4)
            ligne_top  += "+" + "-"*w + "+  "
            ligne_nom  += "|" + nom.center(w)   + "|  "
            ligne_prop += "|" + ("{"+props+"}").center(w) + "|  "
            ligne_bot  += "+" + "-"*w + "+  "

        print(ligne_top)
        print(ligne_nom)
        print(ligne_prop)
        print(ligne_bot)
        print()

    # -- Transitions ------------------------------------------
    print("  TRANSITIONS :")
    print("  " + "-"*50)

    for nom, state in states_dict.items():
        if state.transitions:
            for dest in state.transitions:
                # Détection cycle (self-loop)
                if dest.name == nom:
                    print(f"    {nom}  --(boucle)-->  {nom}")
                else:
                    print(f"    {nom}  -------------->  {dest.name}")
        else:
            print(f"    {nom}  (deadlock - aucune transition)")

    print("  " + "-"*50)
    print()


# ================================================================
# PARTIE 6 - Programme principal Console
# ================================================================

states_dict = {}
all_states  = []

# ================================================================
# NOUVELLES FONCTIONNALITES
# 1. Historique des formules testées
# 2. Export résultats vers fichier .txt
# 3. Exemples TD préchargés (Ex4, Ex5, Ex6, Ex7, Ex8)
# 4. Explication WHY (pourquoi VRAI ou FAUX)
# ================================================================

historique = []   # liste de (formule_txt, formule_obj, resultats_dict)


# ================================================================
# FEATURE 1 — HISTORIQUE
# ================================================================

def ajouter_historique(formule_txt, formula, resultats):
    historique.append((formule_txt, formula, dict(resultats)))
    if len(historique) > 20:
        historique.pop(0)

def afficher_historique():
    if not historique:
        print("\n  !! Historique vide - testez d'abord des formules.")
        return
    print("\n  +==============================================+")
    print("  |          HISTORIQUE DES FORMULES            |")
    print("  +==============================================+")
    for i, (txt, f, res) in enumerate(historique, 1):
        vrais = [n for n,v in res.items() if v]
        faux  = [n for n,v in res.items() if not v]
        print(f"  {i:>2}. {txt:<20} => [V]:{vrais}  [F]:{faux}")
    print("  +----------------------------------------------+")
    print("  Tape le NUMERO pour retester, ou ENTREE pour revenir.")
    choix = input("  Choix : ").strip()
    if choix.isdigit():
        idx = int(choix) - 1
        if 0 <= idx < len(historique):
            txt, f, res = historique[idx]
            return txt
    return None


# ================================================================
# FEATURE 2 — EXPORT .TXT
# ================================================================

def exporter_resultats(nom_exercice="resultats"):
    if not historique:
        print("\n  !! Aucun résultat à exporter - testez d'abord des formules.")
        return

    import datetime
    timestamp = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
    filename  = f"CTL_{nom_exercice}_{timestamp}.txt"

    with open(filename, "w", encoding="utf-8") as f:
        f.write("=" * 60 + "\n")
        f.write("  CTL MODEL CHECKER - Resultats\n")
        f.write(f"  Date : {datetime.datetime.now().strftime('%d/%m/%Y %H:%M')}\n")
        f.write("=" * 60 + "\n\n")

        # System info
        if states_dict:
            f.write("SYSTEME DE TRANSITIONS :\n")
            f.write("-" * 40 + "\n")
            for s in states_dict.values():
                props = "{" + ",".join(sorted(s.propositions)) + "}" if s.propositions else "{}"
                succs = [t.name for t in s.transitions]
                f.write(f"  {s.name:<8} {props:<16} -> {succs}\n")
            f.write("\n")

        f.write("FORMULES TESTEES :\n")
        f.write("-" * 40 + "\n")
        for i, (txt, formula, res) in enumerate(historique, 1):
            vrais = [n for n,v in res.items() if v]
            faux  = [n for n,v in res.items() if not v]
            f.write(f"\n{i}. Formule saisie : {txt}\n")
            f.write(f"   Formule parsed : {formula}\n")
            for nom, val in res.items():
                symb = "[V] VRAI" if val else "[F] FAUX"
                f.write(f"   {nom:<8} => {symb}\n")
            f.write(f"   >> VRAI dans : {vrais if vrais else 'aucun'}\n")
            f.write(f"   >> FAUX dans : {faux  if faux  else 'aucun'}\n")

        f.write("\n" + "=" * 60 + "\n")
        f.write("Généré par CTL Model Checker Pro\n")

    print(f"\n  [V] Export réussi => {filename}")
    print(f"  (fichier sauvegardé dans le même dossier que le programme)")


# ================================================================
# FEATURE 3 — EXEMPLES TD PRECHARGES
# ================================================================

def menu_exemples_td():
    print("\n  +==========================================+")
    print("  |        EXEMPLES TD PRECHARGES           |")
    print("  +==========================================+")
    print("  [1]  Ex4 Fig3  - s1{a} s2{a} s3{a,b} s4{b}")
    print("  [2]  Ex5 Fig4  - s1{a} s2{c} s3{b} s4{b,c} s5{a,b,c}")
    print("  [3]  Ex6 Fig5  - s0{p} s1{p,q} s2{q} s3{p}")
    print("  [4]  Ex7 Fig6  - s0{p} s1{} s2{p,q}")
    print("  [5]  Ex8 M1    - S0{r} S1{r,t} S2{q,r} S3{p,q}")
    print("  [q]  Retour")
    print("  +------------------------------------------+")
    return input("  Choix : ").strip().lower()

def charger_ex4():
    global states_dict, all_states
    s1=State("s1",["a"]); s2=State("s2",["a"])
    s3=State("s3",["a","b"]); s4=State("s4",["b"])
    s1.add_transition(s2); s2.add_transition(s3)
    s3.add_transition(s1); s4.add_transition(s2); s4.add_transition(s3)
    states_dict={"s1":s1,"s2":s2,"s3":s3,"s4":s4}
    all_states=[s1,s2,s3,s4]
    print("\n  [V] Ex4 (Fig3) charge!")
    print("  Formules TD : Eoa | EoEoEoa | A[]b | A[]E<>a | A[](A[bUa]) | E<>(E[bUa])")
    dessiner_graphe(states_dict)

def charger_ex5():
    global states_dict, all_states
    s1=State("s1",["a"]); s2=State("s2",["c"])
    s3=State("s3",["b"]); s4=State("s4",["b","c"]); s5=State("s5",["a","b","c"])
    s1.add_transition(s4); s1.add_transition(s3); s2.add_transition(s4)
    s3.add_transition(s4); s4.add_transition(s3); s4.add_transition(s2)
    s4.add_transition(s5); s5.add_transition(s4)
    states_dict={"s1":s1,"s2":s2,"s3":s3,"s4":s4,"s5":s5}
    all_states=[s1,s2,s3,s4,s5]
    print("\n  [V] Ex5 (Fig4) charge!")
    print("  Formules TD : E<>E[]c | A[]E<>c")
    dessiner_graphe(states_dict)

def charger_ex6():
    global states_dict, all_states
    s0=State("s0",["p"]); s1=State("s1",["p","q"])
    s2=State("s2",["q"]); s3=State("s3",["p"])
    s0.add_transition(s1); s0.add_transition(s2)
    s1.add_transition(s0); s2.add_transition(s1); s3.add_transition(s3)
    states_dict={"s0":s0,"s1":s1,"s2":s2,"s3":s3}
    all_states=[s0,s1,s2,s3]
    print("\n  [V] Ex6 (Fig5 - Kripke 1) charge!")
    print("  Formules TD :")
    print("    1. E[pU(!p&&E[!pUq])]")
    print("    2. E[pU(!p&&A[!pUq])]")
    print("    3. A[pU(!p&&E[!pUq])]")
    print("    4. A[pU(!p&&A[!pUq])]")
    dessiner_graphe(states_dict)

def charger_ex7():
    global states_dict, all_states
    s0=State("s0",["p"]); s1=State("s1",[]); s2=State("s2",["p","q"])
    s0.add_transition(s0); s0.add_transition(s1); s0.add_transition(s2)
    s1.add_transition(s2); s2.add_transition(s0)
    states_dict={"s0":s0,"s1":s1,"s2":s2}
    all_states=[s0,s1,s2]
    print("\n  [V] Ex7 (Fig6 - Kripke KS) charge!")
    print("  Formules TD :")
    print("    E<>q | A<>q | E[]p | A[]q | E[pUq] | A[pUq]")
    print("    A[]E<>(p&&q) | E[]A<>(p&&q)")
    dessiner_graphe(states_dict)

def charger_ex8():
    global states_dict, all_states
    S0=State("S0",["r"]); S1=State("S1",["r","t"])
    S2=State("S2",["q","r"]); S3=State("S3",["p","q"])
    S0.add_transition(S1); S0.add_transition(S3)
    S1.add_transition(S2); S3.add_transition(S2)
    states_dict={"S0":S0,"S1":S1,"S2":S2,"S3":S3}
    all_states=[S0,S1,S2,S3]
    print("\n  [V] Ex8 (M1) charge!")
    print("  Formules TD :")
    print("    A<>t | E<>q | !(E[]r) | A[](r||q)")
    dessiner_graphe(states_dict)

def charger_exemples_td():
    while True:
        choix = menu_exemples_td()
        if   choix == "1": charger_ex4(); break
        elif choix == "2": charger_ex5(); break
        elif choix == "3": charger_ex6(); break
        elif choix == "4": charger_ex7(); break
        elif choix == "5": charger_ex8(); break
        elif choix == "q": break
        else: print("  !! Tape 1-5 ou q.")


# ================================================================
# FEATURE 4 — EXPLICATION WHY (pourquoi VRAI ou FAUX)
# ================================================================

def expliquer_formule(formula, state, checker, profondeur=0):
    """
    Génère une explication textuelle simple du résultat.
    """
    indent = "    " + "  " * profondeur
    result = checker.check(formula, state)
    symb   = "[V]" if result else "[F]"
    props  = "{" + ",".join(sorted(state.propositions)) + "}" if state.propositions else "{}"
    succs  = [s.name for s in state.transitions]

    if isinstance(formula, Atom):
        if result:
            return f"{indent}{symb} '{formula.name}' est dans {props} de {state.name}"
        else:
            return f"{indent}{symb} '{formula.name}' n'est PAS dans {props} de {state.name}"

    elif isinstance(formula, Not):
        inner = checker.check(formula.formula, state)
        inner_symb = "[V]" if inner else "[F]"
        return (f"{indent}{symb} NOT applique a {state.name}\n"
                f"{indent}  => sous-formule {formula.formula} est {inner_symb} dans {state.name}\n"
                f"{indent}  => NOT inverse => {symb}")

    elif isinstance(formula, And):
        l = checker.check(formula.left,  state)
        r = checker.check(formula.right, state)
        return (f"{indent}{symb} AND dans {state.name}\n"
                f"{indent}  gauche {formula.left}  => {'[V]' if l else '[F]'}\n"
                f"{indent}  droite {formula.right} => {'[V]' if r else '[F]'}\n"
                f"{indent}  les deux doivent etre [V] => {symb}")

    elif isinstance(formula, Or):
        l = checker.check(formula.left,  state)
        r = checker.check(formula.right, state)
        return (f"{indent}{symb} OR dans {state.name}\n"
                f"{indent}  gauche {formula.left}  => {'[V]' if l else '[F]'}\n"
                f"{indent}  droite {formula.right} => {'[V]' if r else '[F]'}\n"
                f"{indent}  au moins un doit etre [V] => {symb}")

    elif isinstance(formula, EX):
        if result:
            bon = [s.name for s in state.transitions
                   if checker.check(formula.formula, s)]
            return (f"{indent}{symb} EX dans {state.name} : successeurs={succs}\n"
                    f"{indent}  {formula.formula} est vraie dans : {bon} => il existe => [V]")
        else:
            return (f"{indent}{symb} EX dans {state.name} : successeurs={succs}\n"
                    f"{indent}  {formula.formula} n'est vraie dans AUCUN successeur => [F]")

    elif isinstance(formula, AX):
        if result:
            return (f"{indent}{symb} AX dans {state.name} : successeurs={succs}\n"
                    f"{indent}  {formula.formula} est vraie dans TOUS les successeurs => [V]")
        else:
            mauvais = [s.name for s in state.transitions
                       if not checker.check(formula.formula, s)]
            return (f"{indent}{symb} AX dans {state.name} : successeurs={succs}\n"
                    f"{indent}  {formula.formula} est FAUSSE dans : {mauvais} => [F]")

    elif isinstance(formula, EF):
        if result:
            return (f"{indent}{symb} EF dans {state.name}\n"
                    f"{indent}  Il existe un chemin depuis {state.name} qui atteint {formula.formula} => [V]")
        else:
            return (f"{indent}{symb} EF dans {state.name}\n"
                    f"{indent}  Aucun chemin depuis {state.name} n'atteint {formula.formula} => [F]")

    elif isinstance(formula, AF):
        if result:
            return (f"{indent}{symb} AF dans {state.name}\n"
                    f"{indent}  Sur TOUS les chemins depuis {state.name}, {formula.formula} sera atteinte => [V]")
        else:
            return (f"{indent}{symb} AF dans {state.name}\n"
                    f"{indent}  Il existe un chemin depuis {state.name} qui n'atteint jamais {formula.formula} => [F]")

    elif isinstance(formula, EG):
        if result:
            return (f"{indent}{symb} EG dans {state.name}\n"
                    f"{indent}  Il existe un chemin infini depuis {state.name} ou {formula.formula} reste toujours vraie => [V]")
        else:
            return (f"{indent}{symb} EG dans {state.name}\n"
                    f"{indent}  Sur tout chemin depuis {state.name}, {formula.formula} devient fausse a un moment => [F]")

    elif isinstance(formula, AG):
        if result:
            return (f"{indent}{symb} AG dans {state.name}\n"
                    f"{indent}  Sur TOUS les chemins depuis {state.name}, {formula.formula} reste toujours vraie => [V]")
        else:
            return (f"{indent}{symb} AG dans {state.name}\n"
                    f"{indent}  Il existe un etat accessible depuis {state.name} ou {formula.formula} est fausse => [F]")

    elif isinstance(formula, EU):
        if result:
            return (f"{indent}{symb} EU dans {state.name}\n"
                    f"{indent}  Il existe un chemin : {formula.left} vraie JUSQU'A ce que {formula.right} soit vraie => [V]")
        else:
            return (f"{indent}{symb} EU dans {state.name}\n"
                    f"{indent}  Aucun chemin ne satisfait : {formula.left} jusqu'a {formula.right} => [F]")

    elif isinstance(formula, AU):
        if result:
            return (f"{indent}{symb} AU dans {state.name}\n"
                    f"{indent}  Sur TOUS les chemins : {formula.left} vraie JUSQU'A {formula.right} => [V]")
        else:
            return (f"{indent}{symb} AU dans {state.name}\n"
                    f"{indent}  Il existe un chemin qui ne satisfait pas {formula.left} jusqu'a {formula.right} => [F]")

    return f"{indent}{symb} {formula} dans {state.name}"


def afficher_explication(formula, states_dict, checker):
    print("\n  +--------------------------------------------+")
    print(f"  | WHY : {formula}")
    print("  +--------------------------------------------+")
    for nom, state in states_dict.items():
        expl = expliquer_formule(formula, state, checker)
        print(expl)
    print("  +--------------------------------------------+")


# ================================================================
# MENU PRINCIPAL (mis a jour)
# ================================================================

def sep():
    print("\n" + "="*56)

def afficher_menu():
    sep()
    print("   [?]  CTL MODEL CHECKER  -  Console Pro")
    print("="*56)
    print("  [1]  Creer le systeme (etats + transitions)")
    print("  [2]  Afficher le graphe")
    print("  [3]  Tester une formule CTL")
    print("  [4]  Exemples TD precharges  (Ex4/Ex5/Ex6/Ex7/Ex8)")
    print("  [5]  Aide - symboles clavier")
    print("  [6]  Historique des formules testees")
    print("  [7]  Exporter resultats vers fichier .txt")
    print("  [q]  Quitter")
    print("-"*56)

def afficher_aide():
    print("""
  +======================================================+
  |      SYMBOLES CTL - Style Tina (clavier simple)     |
  +==============+================+=====================+
  | SIGNIFICATION|    SYMBOLE     | EXEMPLE             |
  +==============+================+=====================+
  | Next    E    | Eop            | Eop  Eo(p&&q)       |
  | Next    A    | Aop            | Aop  Ao(p||q)       |
  | Futur   E    | E<>p           | E<>p  E<>(p&&q)     |
  | Futur   A    | A<>p           | A<>p  A<>(p||q)     |
  | Always  E    | E[]p           | E[]p  E[](p&&q)     |
  | Always  A    | A[]p           | A[]p  A[](p||q)     |
  | Until   E    | E[p U q]       | E[pUq]              |
  | Until   A    | A[p U q]       | A[pUq]              |
  +==============+================+=====================+
  | NOT          | !p             | !p   !(p&&q)        |
  | AND          | p&&q           | p&&q                |
  | OR           | p||q           | p||q                |
  +==============+================+=====================+
  |  E = existe (une chemin)   A = pour tous (chemins) |
  +======================================================+
  |  EXEMPLES COMPLEXES :                               |
  |   E<>E[]c      futur toujours c                    |
  |   A[]E<>c      toujours futur c                    |
  |   E[pUq]       p Until q (chemin existe)           |
  |   !p&&q        (non p) et q                        |
  |   A<>(p||q)    futur (p ou q) sur tous chemins     |
  +======================================================+
""")

def etape_creer_systeme():
    global states_dict, all_states
    states_dict = {}
    all_states  = []

    print("\n  -- ÉTAPE 1 : États -------------------------------")
    noms_str  = input("  Noms des états (ex: s0,s1,s2) : ").strip()
    noms      = [n.strip() for n in noms_str.split(",") if n.strip()]
    if not noms:
        print("  !! Aucun état saisi."); return

    print("\n  -- ÉTAPE 2 : Propositions -------------------------")
    print("  (laisse vide si l'état n'a pas de proposition)")
    for nom in noms:
        p_str = input(f"  Props de {nom} (ex: p,q) : ").strip()
        props = [p.strip() for p in p_str.split(",") if p.strip()]
        states_dict[nom] = State(nom, props)
        label = "{" + ",".join(props) + "}" if props else "{{}}"
        print(f"    OK  {nom}  {label}")

    print("\n  -- ÉTAPE 3 : Transitions --------------------------")
    print("  Format : s0->s1,s0->s2,s1->s2  (virgule entre chaque)")
    trans_str = input("  Transitions : ").strip()

    ok, err = [], []
    for t in trans_str.split(","):
        t = t.strip()
        if "->" not in t: continue
        src, dst = t.split("->",1)
        src, dst = src.strip(), dst.strip()
        if src in states_dict and dst in states_dict:
            states_dict[src].add_transition(states_dict[dst])
            ok.append(f"{src}->{dst}")
        else:
            err.append(t)

    all_states = list(states_dict.values())

    print()
    if ok:  print("  OK Transitions : " + "  ".join(ok))
    if err: print("  !! Ignorées    : " + "  ".join(err))

    # Affichage graphe automatique !
    dessiner_graphe(states_dict)



def etape_tester_formule():
    if not states_dict:
        print("\n  !! Cree d'abord un systeme (choix 1 ou 4).")
        return

    checker = CTLModelChecker(all_states)
    print(f"\n  Etats : {list(states_dict.keys())}")
    print("  Symboles : Eop  E<>p  E[]p  E[pUq]  !p  &&  ||")
    print("  Commandes : [h]=historique  [w]=activer WHY  [q]=quitter")
    print()

    mode_why = False

    while True:
        prefix = " [WHY]" if mode_why else ""
        formule_txt = input(f"  Formule CTL{prefix} : ").strip()

        if formule_txt.lower() == 'q':
            break

        if formule_txt.lower() == 'h':
            retest = afficher_historique()
            if retest:
                formule_txt = retest
            else:
                continue

        if formule_txt.lower() == 'w':
            mode_why = not mode_why
            print(f"  >> WHY mode : {'ACTIVE' if mode_why else 'DESACTIVE'}")
            continue

        if not formule_txt:
            continue

        try:
            formula   = parse_formula(formule_txt)
            resultats = checker.check_all(formula, states_dict)
        except ValueError as e:
            print(f"  !! Erreur formule : {e}")
            continue

        ajouter_historique(formule_txt, formula, resultats)

        print()
        print(f"  Formule : {formula}")
        print("  " + "-"*50)
        print(f"  {'Etat':<8} {'Propositions':<20} Resultat")
        print("  " + "-"*50)

        vrais, faux = [], []
        for nom, state in states_dict.items():
            r     = resultats[nom]
            props = "{" + ",".join(sorted(state.propositions)) + "}" if state.propositions else "{}"
            symb  = "[V]  VRAI" if r else "[F]  FAUX"
            print(f"  {nom:<8} {props:<20} {symb}")
            (vrais if r else faux).append(nom)

        print("  " + "-"*50)
        print(f"  [V] VRAI dans : {vrais if vrais else '[ aucun ]'}")
        print(f"  [F] FAUX dans : {faux  if faux  else '[ aucun ]'}")
        print()

        if mode_why:
            afficher_explication(formula, states_dict, checker)


# -- Lancement --------------------------------------------------

if __name__ == "__main__":
    print("\n" + "="*56)
    print("    CTL MODEL CHECKER  -  Console Pro")
    print("    Symboles Tina : Eop  E<>p  E[]p  E[pUq]")
    print("="*56)

    while True:
        afficher_menu()
        choix = input("  Ton choix : ").strip().lower()

        if   choix == "1": etape_creer_systeme()
        elif choix == "2":
            if states_dict: dessiner_graphe(states_dict)
            else: print("\n  !! Aucun systeme charge.")
        elif choix == "3": etape_tester_formule()
        elif choix == "4": charger_exemples_td()
        elif choix == "5": afficher_aide()
        elif choix == "6": afficher_historique()
        elif choix == "7":
            nom = input("  Nom du fichier (ex: Ex4) : ").strip() or "resultats"
            exporter_resultats(nom)
        elif choix == "q":
            print("\n  Au revoir !\n"); break
        else:
            print("  !! Tape 1-7 ou q.")
