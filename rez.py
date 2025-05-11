#!/usr/bin/python3

from typing import List
import sys, itertools
from pysat.solvers import Solver
from pysat.formula import CNF as PySatCNF

class Instance:
    def __init__(self, n: int, m: int, adj):
        self._n = n
        self._m = m
        self._adj = adj

    def vertex_number(self) -> int:
        return self._n

    def edge_number(self) -> int:
        return self._m

    def adj(self, v) -> List[int]:
        return self._adj[v]

    def edges(self):
        for v in range(self.vertex_number()):
            for u in self.adj(v):
                if v < u:
                    yield (v, u)

    def vertex_set(self):
        return range(self.vertex_number())

    def __repr__(self):
        return "Instance({}, {})".format(self.vertex_number(), list(self.edges()))

class Result:
    def __init__(self, depth: int, parents: List[int]):
        self._parents = parents
        self._depth = depth

    def depth(self):
        return self._depth

    def parent(self, i: int) -> int:
        return self._parents[i]

    def __repr__(self):
        return "Result({}, {})".format(self.depth(), self._parents)

def read_instance(filepath: str) -> Instance:
    try:
        formula = PySatCNF(from_file=filepath)
    except Exception as e:
        sys.exit(f"Eroare la parsarea fișierului CNF '{filepath}' cu PySAT: {e}")
        
    num_vars = formula.nv 
    
    if num_vars == 0 and not formula.clauses:
       
         return Instance(0, 0, [])


    adj = [set() for _ in range(num_vars)]

    for clause in formula.clauses:
        current_clause_vars = []
        for literal in clause:
            abs_var = abs(literal)
            if 1 <= abs_var <= num_vars:
                current_clause_vars.append(abs_var - 1) 
     
        
        unique_vars_in_clause = sorted(list(set(current_clause_vars)))
        
        for i in range(len(unique_vars_in_clause)):
            for j in range(i + 1, len(unique_vars_in_clause)):
                u, v = unique_vars_in_clause[i], unique_vars_in_clause[j]
                adj[u].add(v)
                adj[v].add(u)
    
    final_adj = [list(s) for s in adj]
    
    actual_m = 0
    for u_val in range(num_vars):
        actual_m += len(final_adj[u_val])
    actual_m //= 2

   
    return Instance(num_vars, actual_m, final_adj)


def print_result(out, instance: Instance, result: Result):
    if not isinstance(result, Result):
         sys.exit(f"Error: Invalid result type: {type(result)}")

    print(result.depth())
    for i in range(instance.vertex_number()):
        parent_val = result.parent(i)
        if parent_val == -1:
            print(0) 
        else:
            print(parent_val + 1)

def make_solver():
    return Solver(name='Glucose4')

def solve_limited_with_sat(instance: Instance, mi: int):
    if instance.vertex_number() == 0:
        return lambda: Result(0, [])

    solver: Solver = make_solver()
    n: int = instance.vertex_number()
    length: int = mi + 1

    def flat_var(a: int, b: int, c: int) -> int:
        v1, v2 = min(a,b), max(a,b)
        return 1 + ((v1 * n + v2) * length + c)

    for v_node in range(n):
        for u_node in range(n):
            for w_node in range(n):
                for i in range(1, length):
                    if v_node != u_node and u_node != w_node and v_node != w_node:
                        solver.add_clause([-flat_var(v_node, u_node, i), -flat_var(u_node, w_node, i), flat_var(v_node, w_node, i)])
                        solver.add_clause([-flat_var(v_node, w_node, i), -flat_var(w_node, u_node, i), flat_var(v_node, u_node, i)])
                        solver.add_clause([-flat_var(u_node, v_node, i), -flat_var(v_node, w_node, i), flat_var(u_node, w_node, i)])

    for v_node in range(n):
        for u_node in range(v_node, n):
            solver.add_clause([-flat_var(v_node, u_node, 0)])
            if n > 0:
                solver.add_clause([flat_var(v_node, u_node, length - 1)])

    for v_node in range(n):
        for u_node in range(v_node, n):
            for i in range(1, length):
                solver.add_clause([-flat_var(v_node, u_node, i - 1), flat_var(v_node, u_node, i)])

    for v_idx in range(n):
        for u_idx in range(v_idx + 1, n):
            for i in range(1, length):
                solver.add_clause([-flat_var(v_idx, u_idx, i), flat_var(v_idx, v_idx, i - 1), flat_var(u_idx, u_idx, i - 1)])

    for (v_edge, u_edge) in instance.edges():
        min_vu, max_vu = min(v_edge, u_edge), max(v_edge, u_edge)
        for i in range(1, length):
            solver.add_clause([-flat_var(min_vu, min_vu, i), -flat_var(max_vu, max_vu, i),
                               flat_var(min_vu, min_vu, i - 1), flat_var(min_vu, max_vu, i)])
            solver.add_clause([-flat_var(min_vu, min_vu, i), -flat_var(max_vu, max_vu, i),
                               flat_var(max_vu, max_vu, i - 1), flat_var(min_vu, max_vu, i)])

    if not solver.solve():
        return None

    true_set = set(filter(lambda x: x > 0, solver.get_model()))
    
    def recover():
        first_time = [-1 for _ in range(n)]
        for i_level_ft in range(length - 1, 0, -1): 
            for v_node_ft in range(n):
                if flat_var(v_node_ft, v_node_ft, i_level_ft) in true_set:
                    if first_time[v_node_ft] == -1: 
                        first_time[v_node_ft] = i_level_ft

        parents = [-1 for _ in range(n)]
        
        sorted_nodes_to_process = sorted(enumerate(first_time), key=lambda x: (x[1], x[0]))

        for v_node_idx, tm in sorted_nodes_to_process:
            if tm == -1: 
                continue
            
            if tm != -1 : 
                for u_child_idx in range(n):
                    if u_child_idx != v_node_idx and parents[u_child_idx] == -1:
                        if first_time[u_child_idx] != -1 and first_time[u_child_idx] >= tm :
                             if flat_var(v_node_idx, u_child_idx, first_time[u_child_idx]) in true_set: 
                                parents[u_child_idx] = v_node_idx
        
        if n > 0 and parents.count(-1) == 0:
            min_tm_val = n + 2 
            root_candidate = -1
            for idx_rt in range(n):
                if first_time[idx_rt] != -1:
                    if root_candidate == -1 or first_time[idx_rt] < min_tm_val:
                        min_tm_val = first_time[idx_rt]
                        root_candidate = idx_rt
                    elif first_time[idx_rt] == min_tm_val and idx_rt < root_candidate: 
                        root_candidate = idx_rt
            if root_candidate != -1:
                parents[root_candidate] = -1
        return Result(mi, parents)
    return recover

def solve(instance: Instance) -> Result:
    if instance.vertex_number() == 0:
        return Result(0, [])
    if instance.vertex_number() == 1:
        return Result(0, [-1]) 

    lo: int = 0 
    hi: int = 1
    recover_func = None
    max_hi_tries = instance.vertex_number() if instance.vertex_number() > 0 else 1
    tries = 0

    while tries < max_hi_tries:
        tries += 1
        current_recover = solve_limited_with_sat(instance, hi)
        if current_recover:
            recover_func = current_recover
            break
        lo = hi
        hi *= 2
        if hi >= instance.vertex_number() and instance.vertex_number() > 0 : 
            target_hi = instance.vertex_number() - 1
            if target_hi < 0: target_hi = 0 
            if target_hi <= lo and lo + 1 < instance.vertex_number(): hi = lo + 1
            elif target_hi <= lo : hi = target_hi 
            else: hi = target_hi

            current_recover = solve_limited_with_sat(instance, hi)
            if current_recover:
                recover_func = current_recover
            break 
    else: 
        if not recover_func: 
            final_attempt_hi = instance.vertex_number() - 1
            if final_attempt_hi < 0: final_attempt_hi = 0
            if instance.vertex_number() > 0 and (tries >= max_hi_tries or hi != final_attempt_hi) :
                 current_recover = solve_limited_with_sat(instance, final_attempt_hi)
                 if current_recover:
                     recover_func = current_recover
                     hi = final_attempt_hi 
            if not recover_func:
                 sys.exit("Error: Could not find any solution even with max depth.")
    
    if not recover_func: 
        sys.exit("Error: Initial solution search failed.")

    final_hi = hi 
    
    if lo >= final_hi : 
        final_solution_recover = solve_limited_with_sat(instance, final_hi)
        if final_solution_recover:
            return final_solution_recover()
        elif recover_func : 
            return recover_func()
        else: 
             sys.exit("Error: No initial solution for binary search phase.")


    while final_hi - lo > 1: 
        mi: int = lo + (final_hi - lo) // 2
        if mi <= lo : mi = lo + 1 
        if mi >= final_hi : break      

        rs_recover = solve_limited_with_sat(instance, mi)
        if rs_recover:
            final_hi = mi 
            recover_func = rs_recover
        else:
            lo = mi 
    
    final_solution_recover = solve_limited_with_sat(instance, final_hi)
    if final_solution_recover:
        return final_solution_recover()
    elif recover_func: 
        return recover_func()

    sys.exit("Error: Failed to recover final solution after binary search.")

def main():
    instance: Instance = None
    input_filename = "test.cnf"


    try:
        instance = read_instance(input_filename)
    except FileNotFoundError:
        sys.exit(f"EROARE: Fișierul '{input_filename}' nu a fost găsit.")
    except Exception as e:
        sys.exit(f"EROARE la procesarea fișierului '{input_filename}': {e}")

    if instance is None: 
        sys.exit("EROARE: Instanța nu a putut fi încărcată.")

    result: Result = solve(instance)
    print_result(sys.stdout, instance, result)

if __name__ == '__main__':
    main()