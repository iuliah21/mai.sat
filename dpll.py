#!/usr/bin/python3

import random
import sys
import time
import copy
from collections import OrderedDict

class Clauza:
    def __init__(self):
        pass

    def din_lista_literali(self, lista_literali_int):
        self.simboluri = {}
        for literal_int in lista_literali_int:
            index_variabila = abs(literal_int)
            semn = 1 if literal_int > 0 else -1
            self.simboluri[index_variabila] = semn

    def __str__(self):
        tokens = []
      
        simboluri_sortate = sorted(self.simboluri.items())
        for index_variabila, semn in simboluri_sortate:
            token = ""
            if semn == -1:
                token += "-"
            token += str(index_variabila)
            tokens.append(token)
        return " ".join(tokens)

class InstantaSAT:
    def __init__(self):
        pass

    def incarca_din_fisier_dimacs(self, cale_fisier):
        self.variabile_declarate_index = [] 
        self.clauze = []
        self.num_variabile_din_header = 0
        
        try:
            with open(cale_fisier, "r") as fisier:
                for linie_text in fisier:
                    linie_text_curatata = linie_text.strip()
                    if not linie_text_curatata or linie_text_curatata.startswith('c'):
                        continue
                    
                    parti = linie_text_curatata.split()
                    if not parti:
                        continue

                    if parti[0] == 'p':
                        if len(parti) == 4 and parti[1] == "cnf":
                            try:
                                self.num_variabile_din_header = int(parti[2])
                              
                            except ValueError:
                                print(f"Eroare: Linia 'p' conține valori non-numerice: {linie_text_curatata}", file=sys.stderr)
                                sys.exit(1)
                        else:
                            print(f"Eroare: Linia 'p' este malformată: {linie_text_curatata}", file=sys.stderr)
                            sys.exit(1)
                        continue

                    literali_clauza_curenta = []
                    try:
                        for token_literal in parti:
                            val_literal = int(token_literal)
                            if val_literal == 0:
                                break 
                            literali_clauza_curenta.append(val_literal)
                    except ValueError:
                        print(f"Eroare: Clauză malformată (literal non-numeric): {linie_text_curatata}", file=sys.stderr)
                        continue 

                    if literali_clauza_curenta:
                        clauza_noua = Clauza()
                        clauza_noua.din_lista_literali(literali_clauza_curenta)
                        self.clauze.append(clauza_noua)
        except FileNotFoundError:
            print(f"Eroare: Fișierul '{cale_fisier}' nu a fost găsit.", file=sys.stderr)
            sys.exit(1)
        except Exception as e:
            print(f"Eroare la citirea fișierului '{cale_fisier}': {e}", file=sys.stderr)
            sys.exit(1)

        if self.num_variabile_din_header > 0:
            self.variabile_declarate_index = list(range(1, self.num_variabile_din_header + 1))
        else:
           
            toate_variabilele_vazute = set()
            for clauza_obj in self.clauze:
                for var_idx in clauza_obj.simboluri.keys():
                    toate_variabilele_vazute.add(var_idx)
            if toate_variabilele_vazute:
                self.num_variabile_din_header = max(toate_variabilele_vazute)
                self.variabile_declarate_index = list(range(1, self.num_variabile_din_header + 1))
            else: 
                 self.variabile_declarate_index = []


    def __str__(self):
        s = []
        for clauza_obj in self.clauze:
            s.append(str(clauza_obj))
        return "\n".join(s)

    def este_satisfacuta(self, atribuire_completa: dict) -> bool:
        for clauza_obj in self.clauze:
            clauza_este_adevarata = False
            for index_variabila, semn_necesar in clauza_obj.simboluri.items():
                if index_variabila in atribuire_completa:
                    if atribuire_completa[index_variabila] == semn_necesar:
                        clauza_este_adevarata = True
                        break 
            if not clauza_este_adevarata:
                return False 
        return True 

    def gaseste_clauza_unitara(self):
        for clauza_obj in self.clauze:
            if len(clauza_obj.simboluri) == 1:
                index_variabila = next(iter(clauza_obj.simboluri.keys()))
                semn = next(iter(clauza_obj.simboluri.values()))
                return {index_variabila: semn}
        return None 

    def nu_exista_clauza_unitara_opusa(self, clauza_unitara_dict):
        index_variabila_referinta = next(iter(clauza_unitara_dict.keys()))
        semn_referinta = next(iter(clauza_unitara_dict.values()))

        for clauza_obj in self.clauze:
            if len(clauza_obj.simboluri) == 1:
                index_variabila_curent = next(iter(clauza_obj.simboluri.keys()))
                semn_curent = next(iter(clauza_obj.simboluri.values()))
                if index_variabila_curent == index_variabila_referinta and semn_curent != semn_referinta:
                    return False 
        return True 

    def simplifica(self, clauza_unitara_dict):
        index_var_propagat = next(iter(clauza_unitara_dict.keys()))
        semn_propagat = next(iter(clauza_unitara_dict.values()))
        
        clauze_noi = []
        conflict_detectat = False

        for clauza_obj in self.clauze:
            if index_var_propagat in clauza_obj.simboluri:
                if clauza_obj.simboluri[index_var_propagat] == semn_propagat:
                    continue 
                else: 
                    clauza_modificata = Clauza()
                    clauza_modificata.simboluri = clauza_obj.simboluri.copy()
                    del clauza_modificata.simboluri[index_var_propagat]
                    if not clauza_modificata.simboluri: 
                        conflict_detectat = True
                        break 
                    clauze_noi.append(clauza_modificata)
            else:
                clauze_noi.append(clauza_obj)
        
        if conflict_detectat:
            self.clauze = [Clauza()] 
        
        else:
            self.clauze = clauze_noi
        return self

def rezolva_dpll(instanta_initiala):
    instanta_de_lucru = copy.deepcopy(instanta_initiala)
    atribuire_rezultat = dpll_recursiv(instanta_de_lucru, {})
    
    if atribuire_rezultat is not None:
        atribuire_completa = atribuire_rezultat.copy()
        for var_idx in instanta_initiala.variabile_declarate_index:
            if var_idx not in atribuire_completa:
                atribuire_completa[var_idx] = 1 
        
        atribuire_sortata = dict(OrderedDict(sorted(atribuire_completa.items())))
        return atribuire_sortata
    else:
        return None


def dpll_recursiv(instanta, atribuire_curenta):
    if not instanta.clauze:
        return atribuire_curenta

  
    while True:
        clauza_unit = instanta.gaseste_clauza_unitara()
        if not clauza_unit:
            break 

        if instanta.nu_exista_clauza_unitara_opusa(clauza_unit) == False:
            return None 
        
        simbol_idx_unitar = next(iter(clauza_unit.keys()))
        semn_unitar = next(iter(clauza_unit.values()))

   
        if simbol_idx_unitar in atribuire_curenta and atribuire_curenta[simbol_idx_unitar] != semn_unitar:
            return None 

        atribuire_curenta[simbol_idx_unitar] = semn_unitar
        instanta.simplifica(clauza_unit)

        if not instanta.clauze:
            return atribuire_curenta
        if any(not cl.simboluri for cl in instanta.clauze):
            return None 

    variabila_aleasa = None
    for var_idx_potential in instanta.variabile_declarate_index: 
        if var_idx_potential not in atribuire_curenta:
            variabila_aleasa = var_idx_potential
            break
    
    if variabila_aleasa is None:
     
        return None 

 
    for semn_ales in [1, -1]:
        instanta_copie_ramura = copy.deepcopy(instanta)
        atribuire_copie_ramura = atribuire_curenta.copy()
        
        dict_variabila_aleasa = {variabila_aleasa: semn_ales}
   
        atribuire_copie_ramura[variabila_aleasa] = semn_ales
        instanta_copie_ramura.simplifica(dict_variabila_aleasa)

 
        if any(not cl.simboluri for cl in instanta_copie_ramura.clauze):
            continue 

        rezultat_recursiv = dpll_recursiv(instanta_copie_ramura, atribuire_copie_ramura)
        if rezultat_recursiv is not None:
            return rezultat_recursiv
            
    return None
						
def principal(cale_fisier_input):
    instanta = InstantaSAT()
    instanta.incarca_din_fisier_dimacs(cale_fisier_input)
    
   

    atribuire = rezolva_dpll(instanta)
    
    with open("assignments.txt", "w") as fisier_iesire:
        if atribuire is not None:
         
            tokens_atribuire = []
            for index_variabila, semn in atribuire.items():
                token = ""
                if semn == -1:
                    token += "-"
                token += str(index_variabila)
                tokens_atribuire.append(token)
            fisier_iesire.write(" ".join(tokens_atribuire) + "\n")
        else:
            
            fisier_iesire.write("UNSATISFIABLE\n")

if __name__ == "__main__":
    if len(sys.argv) > 1:
        nume_fisier = sys.argv[1]
        principal(nume_fisier)
    else:
       
        principal("test.cnf")