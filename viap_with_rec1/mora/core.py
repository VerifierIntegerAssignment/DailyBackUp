from diofant import prod, Symbol
from mora.utils import Update
from .solver import solve_recurrences
from typing import List, Dict


class Program:
    def __init__(self):
        self.name: str = ""
        self.source: str = ""
        self.variables: List[Symbol] = []
        self.initial_values: Dict[Symbol, Update] = {}
        self.updates: Dict[Symbol, Update] = {}
        self.goals: List[int] = []


def core(program: Program, goal: int = 1):
    vars = program.variables
    rvars = vars[::-1]
    initial = program.initial_values
    updates = program.updates

    S = set_goal(goal, vars)

    print('----------------------------')
    print(vars)
    print(initial)
    print(updates)
    #print(type(program))
    #print(S)
    #print(initial)
    for x in updates:
        y=updates[x]
        #y.displayAll()
        print(y)
        print(y.is_random_var)
        print(y.random_var)
        print(y.var)
        print(y.branches)
        for z in y.branches:
            k,h = z
            print(k)
            print(h)
            print(type(k))
            print('++++++')
        print('%%%%%%%%%%%%%%%%%')
    print(rvars)
    print('----------------------------')

    program.goals = {s for s in S}

    MBRecs = dict()
    while S:
        M = S.pop()
        M_orig = M
        M = M.as_poly(rvars)
        #print('----------------------------')
        #print(M)
        #print(S)
        #print('----------------------------')
        for i, var in enumerate(rvars):
            M = M.as_poly(var)
            terms = [ (coeff*var**mono[0]).as_poly(var) for coeff, mono in zip(M.coeffs(), M.monoms())]
            for j, term in enumerate(terms):
                pow = term.monoms()[0][0] # power of var in term
                terms[j] = updates[var].update_term(term, pow).as_poly(rvars)
            M = sum(terms).as_poly(rvars)

        MBRecs[M_orig] = M
        #print('----------------------------@')
        #print(M_orig)
        #print('----------------------------')
        #print(M)
        #print(M.monoms())
        #print('----------------------------@')

        for mono in M.monoms():
            N = prod(v**pow for v, pow in zip(M.gens, mono))
            if N not in MBRecs and N != 1:
                S.add(N)

    print(' --- MBRecs --- ')
    for k, v in MBRecs.items():
        print(' '*3, k, ' = ', v.as_expr())
    print()

    return solve_recurrences(MBRecs, rvars, init=initial)


def set_goal(goal, vars):
    print("setting goal: ", goal)
    goal = int(goal)
    print(goal)
    S = {x**goal for x in vars}
    return S
