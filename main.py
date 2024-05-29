import itertools
from os import remove
from model import *
from utils import *

def alg(constraints: list[Constraint]) -> Renaming:
    constraint = None
    for i, c in enumerate(constraints):
        constraints[i] = Constraint(organize(c.left), organize(c.right))
        if not isBasic(c) and constraint is None:
            constraint = c
    
    if constraint is None:
        return solve(constraints)
    
    t, s = constraint.left, constraint.right
    # t = reduce(t)
    # s = reduce(s)

    return Renaming([])

def solve(constraints: list[Constraint]) -> Renaming:
    return Renaming([])


def normalForm(t: Type) -> Type:
    return removeDuplicates(typeSort(t))

def recomb(t: Type, s: Type) -> Renaming | None:
    t = normalForm(t)
    s = normalForm(s)

    solution: dict[Variable, Variable] = {}

    def matchType(t: Type, s: Type) -> bool:
        nonlocal solution
        match t, s:
            case Variable(_) as a, Variable(_) as b:
                if a not in solution:
                    solution[a] = b
                    return True
                else:
                    return solution[a] == b
            case Arrow(l1, r1), Arrow(l2, r2):
                localCopy = dict(solution)
                if matchType(l1, l2):
                    if matchType(r1, r2):
                        return True
                    else:
                        solution = localCopy
                return False
            case Intersection(types1), Intersection(types2):
                return matchTypes(types1, types2)
            case _, _:
                return False

        assert False

    # sppedups: numpy, recursive pass of solutions, smart copy, BFS!!!

    def matchTypes(types1: list[Type], types2: list[Type]) -> bool:
        nonlocal solution
        if len(types1) != len(types2):
            return False
        if not types1:
            return True
        t = types1[0]
        for i, s in enumerate(types2):
            localCopy = dict(solution)
            if matchType(t, s):
                if matchTypes(types1[1:], types2[:i] + types2[i + 1:]):
                    return True
                else:
                    solution = localCopy
        return False
    
    if matchType(t, s):
        return Renaming([[k, v] for k, v in solution.items()])
    return None


def getRenaming(sVars: list[Variable], current: Renaming, index: int, stop: int):
    if index == stop:
        yield current
        return

    init = sVars[0]
    for v in sVars:
        current.subs[index][1] = v
        yield from getRenaming(sVars, current, index + 1, stop)

        for i in range(index + 1, stop):
            current.subs[i][1] = init

def checkRenaming(s: Renaming, sVars: list[Variable]) -> bool:
    for b in sVars:
        if s.inverse(b) is None:
            return False
    return True

def naiveComparison(t: Type, s: Type) -> Renaming | None:
    t = typeSort(t)
    t = removeDuplicates(t)
    s = typeSort(s)
    s = removeDuplicates(s)

    tVars = getVars(t)
    sVars = getVars(s)

    if not sVars: # nothing to match against
        if t == s:
            return Renaming([])
        return None
    
    sVarsList = list(sVars)
    init = sVarsList[0]
    current = Renaming([[a, init] for a in tVars])
    g = getRenaming(sVarsList, current, 0, len(tVars))

    for renaming in g:
    # renaming = Renaming([[a, init] for a in tVars])
    # for p in itertools.permutations(sVarsList):
    #     for i in range(len(renaming.subs)):
    #         renaming.subs[i][1] = p[i]
        if not checkRenaming(renaming, sVarsList):
            continue

        t1 = typeSort(renaming.applyTo(t))
        if t1 == s:
            return renaming
    
    return None
