import re

class Unitate:
    def __init__(self, valoare_str):
        self.valoare = valoare_str
        self.negat = False

    def tiparibil(self):
        return "~" + self.valoare if self.negat else self.valoare

    def __lt__(self, other):
        if not isinstance(other, Unitate):
            return NotImplemented
        try:
            val_self_int = int(self.valoare)
            val_other_int = int(other.valoare)
            if val_self_int != val_other_int:
                return val_self_int < val_other_int
            return self.negat < other.negat
        except ValueError:
            if self.valoare != other.valoare:
                return self.valoare < other.valoare
            return self.negat < other.negat

    def __eq__(self, other):
        if not isinstance(other, Unitate):
            return NotImplemented
        return self.valoare == other.valoare and self.negat == other.negat

    def __hash__(self):
        return hash((self.valoare, self.negat))

class Clauza:
    def __init__(self, unitati_initiale):
        self.unitati = []
        self.is_tautology = False

        if not unitati_initiale:
            return

        unitati_unice_temp = []
        vazute_pt_unicitate = set()
        for u_in in unitati_initiale:
            repr_u = (u_in.valoare, u_in.negat)
            if repr_u not in vazute_pt_unicitate:
                unitati_unice_temp.append(u_in)
                vazute_pt_unicitate.add(repr_u)

        literali_map = {}
        for u in unitati_unice_temp:
            if u.valoare not in literali_map:
                literali_map[u.valoare] = {'pos': False, 'neg': False}

            if u.negat:
                literali_map[u.valoare]['neg'] = True
            else:
                literali_map[u.valoare]['pos'] = True

            if literali_map[u.valoare]['pos'] and literali_map[u.valoare]['neg']:
                self.is_tautology = True
                self.unitati = []
                return

        if not self.is_tautology:
            self.unitati = sorted(unitati_unice_temp)

    def tiparibil(self):
        if self.is_tautology:
            return "(TAUTOLOGY)"
        if not self.unitati:
            return "[]"
        return r'({})'.format(' \/ '.join([u.tiparibil() for u in self.unitati]))

    def __eq__(self, other):
        if not isinstance(other, Clauza):
            return NotImplemented
        if self.is_tautology and other.is_tautology:
            return True
        if self.is_tautology != other.is_tautology:
            return False
        return self.unitati == other.unitati

    def __hash__(self):
        if self.is_tautology:
            return hash((True,))
        return hash(tuple(self.unitati))

    def get_canonical_representation_for_sorting(self):
        if self.is_tautology:
            return (2, float('inf'))
        if not self.unitati:
            return (0, 0)
        return (1, len(self.unitati))

class Expresie:
    def __init__(self, clauze):
        self.clauze = [c for c in clauze if not c.is_tautology]
        self.satisfiabila = None

    def tipareste(self, show_clauses=False):
        print(f'Expresie CNF: {self.tiparibil_sumar()}')
        if self.satisfiabila is None:
            print('Satisfiabilitate: Necunoscută (rulează aplica_rezolutie())')
        elif self.satisfiabila:
            print('Satisfiabilitate: DA')
        else:
            print('Satisfiabilitate: NU')

        if show_clauses:
            print("Clauze curente:")
            clauze_sortate = sorted(self.clauze, key=lambda cl: cl.get_canonical_representation_for_sorting())
            for c in clauze_sortate:
                print(f"  {c.tiparibil()}")

    def tiparibil_sumar(self):
        num_total = len(self.clauze)
        num_taut = sum(1 for c in self.clauze if c.is_tautology)
        num_empty = sum(1 for c in self.clauze if not c.unitati and not c.is_tautology)
        return f"{num_total} clauze (din care {num_taut} tautologii, {num_empty} clauze vide)"

    def tiparibil(self):
        clauze_de_afisat = sorted(self.clauze, key=lambda cl: cl.get_canonical_representation_for_sorting())
        limit = 20

        if not clauze_de_afisat:
            return "(EMPTY EXPRESSION - SATISFIABLE)"

        repr_list = [c.tiparibil() for c in clauze_de_afisat[:limit]]

        if len(clauze_de_afisat) > limit:
            repr_list.append(f"... și încă {len(clauze_de_afisat) - limit} clauze")

        return ' /\\ '.join(repr_list)

    def aplica_rezolutie(self):
        self.satisfiabila = True

        active_clauses = set(c for c in self.clauze if not c.is_tautology)

        if not active_clauses:
            self.clauze = []
            self.satisfiabila = True
            return

        for clauza in active_clauses:
            if not clauza.unitati:
                self.satisfiabila = False
                self.clauze = list(active_clauses)
                return

        iteration_count = 0
        while True:
            iteration_count += 1
            new_resolvents_generated_this_iteration = set()

            list_of_active_clauses = sorted(list(active_clauses), key=lambda c: c.get_canonical_representation_for_sorting())
            num_active = len(list_of_active_clauses)

            for i in range(num_active):
                ci = list_of_active_clauses[i]
                if not ci.unitati: continue

                for j in range(i + 1, num_active):
                    cj = list_of_active_clauses[j]
                    if not cj.unitati: continue

                    for idx_u1_ci, u1_ci in enumerate(ci.unitati):
                        for idx_u2_cj, u2_cj in enumerate(cj.unitati):
                            if u1_ci.valoare == u2_cj.valoare and u1_ci.negat != u2_cj.negat:
                                potential_new_clause_units = []
                                for k_ci, unit_in_ci in enumerate(ci.unitati):
                                    if k_ci != idx_u1_ci:
                                        potential_new_clause_units.append(unit_in_ci)

                                for k_cj, unit_in_cj in enumerate(cj.unitati):
                                    if k_cj != idx_u2_cj:
                                        potential_new_clause_units.append(unit_in_cj)

                                resolvent = Clauza(potential_new_clause_units)

                                if not resolvent.unitati and not resolvent.is_tautology:
                                    self.satisfiabila = False
                                    active_clauses.add(resolvent)
                                    self.clauze = list(active_clauses)
                                    return

                                if not resolvent.is_tautology and resolvent not in active_clauses:
                                    new_resolvents_generated_this_iteration.add(resolvent)

            if not new_resolvents_generated_this_iteration:
                self.clauze = list(active_clauses)
                return

            active_clauses.update(new_resolvents_generated_this_iteration)


def citeste_clauze_fisier(nume_fisier):
    clauze_obiecte = []
    try:
        with open(nume_fisier, "r") as fisier:
            linii = fisier.readlines()
            num_clauses_declared = 0
            parsed_header = False
            for linie_str in linii:
                linie_str = linie_str.strip()
                if not linie_str or linie_str.startswith('c') or linie_str.startswith('%') or linie_str == '0':
                    continue

                if linie_str.startswith('p cnf'):
                    if parsed_header:
                        print(f"Avertisment: Linie 'p cnf' multiplă găsită. Se ignoră: '{linie_str}'")
                        continue
                    try:
                        parts = linie_str.split()
                        if len(parts) >= 4:
                            num_clauses_declared = int(parts[3])
                            parsed_header = True
                        else:
                             print(f"Avertisment: Linia 'p cnf' este incompletă: '{linie_str}'")
                    except (IndexError, ValueError) as e:
                        print(f"Avertisment: Linia 'p cnf' nu a putut fi parcursă: '{linie_str}'. Eroare: {e}")
                    continue

                literali_str = linie_str.split()

                if not literali_str or literali_str[-1] != '0':
                    if literali_str:
                         print(f"Avertisment: Linia de clauză nu se termină cu 0 sau e invalidă: '{linie_str}' - se ignoră.")
                    continue

                unitati_pt_clauza_curenta = []
                valid_clause_line = True
                for literal_str in literali_str[:-1]:
                    if not literal_str: continue
                    try:
                        val_int = int(literal_str)
                        if val_int == 0:
                            print(f"Avertisment: Literal '0' găsit înainte de sfârșitul liniei de clauză: '{linie_str}' - se ignoră clauza.")
                            valid_clause_line = False
                            break

                        unit = Unitate(str(abs(val_int)))
                        if val_int < 0:
                            unit.negat = True
                        unitati_pt_clauza_curenta.append(unit)
                    except ValueError:
                        print(f"Avertisment: Ignor literal invalid '{literal_str}' în linia '{linie_str}'")
                        continue

                if valid_clause_line and unitati_pt_clauza_curenta:
                    clauze_obiecte.append(Clauza(unitati_pt_clauza_curenta))

            if parsed_header and len(clauze_obiecte) != num_clauses_declared:
                print(f"Avertisment: Numărul de clauze citite ({len(clauze_obiecte)}) diferă de cel declarat în antet ({num_clauses_declared}).")

    except FileNotFoundError:
        print(f"EROARE: Fișierul '{nume_fisier}' nu a fost găsit.")
        return None
    except Exception as e:
        print(f"EROARE la citirea fișierului '{nume_fisier}': {e}")
        return None
    return clauze_obiecte

if __name__ == "__main__":
    cnf_file_to_process = "test.cnf"

    print(f"--- Procesare fișier: {cnf_file_to_process} ---")
    clauze_citite = citeste_clauze_fisier(cnf_file_to_process)

    expresie_obj = None

    if clauze_citite is not None:
        num_clauses_read = len(clauze_citite)
        print(f"Au fost citite {num_clauses_read} clauze.")

        if num_clauses_read == 0 and not any(line.strip() and not line.strip().startswith('c') and not line.strip().startswith('p') for line in open(cnf_file_to_process)):
            print("Fișierul nu conține clauze valide sau este gol. Se consideră satisfiabil.")
            expresie_obj = Expresie([])
            expresie_obj.satisfiabila = True
        else:
            expresie_obj = Expresie(clauze_citite)

        print("Expresie inițială:")
        expresie_obj.tipareste(show_clauses=(num_clauses_read < 25))

        if expresie_obj.satisfiabila is None:
            print("\nAplicare rezoluție...")
            try:
                expresie_obj.aplica_rezolutie()
            except Exception as e:
                print(f"EROARE în timpul expresie_obj.aplica_rezolutie(): {e}")
                import traceback
                traceback.print_exc()

        print("\nRezultat final:")
        expresie_obj.tipareste(show_clauses=True)
    else:
        print(f"Procesarea fișierului {cnf_file_to_process} a eșuat sau fișierul nu conține clauze valide.")