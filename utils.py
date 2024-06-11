from model import *
import random
from functools import reduce

def typeSort(t: Type) -> Type:
    match t:
        case Variable(_) as a: 
            return a
        case Intersection(types):
            return Intersection(sorted(typeSort(t) for t in types))
        case Arrow(l, r):
            return Arrow(typeSort(l), typeSort(r))
    assert False

def typeSize(t: Type) -> int:
    match t:
        case Variable(_): return 1
        case Arrow(l, r): return 1 + typeSize(l) + typeSize(r)
        case Intersection(types): return reduce(lambda s, t: s + typeSize(t), types, 1)
    assert(False)

def varsCount(t: Type) -> int:
    match t:
        case Variable(_): return 1
        case Arrow(l, r): return varsCount(l) + varsCount(r)
        case Intersection(types): return reduce(lambda c, t: c + varsCount(t), types, 0)
    assert(False)

def getVars(t: Type) -> set[Variable]:
    match t:
        case Variable(_):
            return {t}
        case Arrow(l, r):
            return getVars(l).union(getVars(r))
        case Intersection(types):
            return reduce(lambda vs1, vs2: vs1.union(vs2), map(getVars, types), set())
    assert False

def removeDuplicates(t: Type) -> Type:
    match t:
        case Variable(_):
            return t
        case Arrow(left, right):
            return Arrow(removeDuplicates(left), removeDuplicates(right))
        case Intersection([]): 
            return t
        case Intersection(types): 
            types = list(map(removeDuplicates, types))
            for i in range(len(types) - 1, 0, -1):
                if types[i] == types[i - 1]:
                    types.pop(i)
            return Intersection(types)
    assert False

def normalForm(t: Type) -> Type:
    return typeSort(removeDuplicates(typeSort(t)))

def randomRename(t: Type, allowedVars: list[Variable] | None = None, unique: bool = True) -> tuple[Type, Renaming]:
    vars = getVars(t)
    if allowedVars is None:
        allowedVars = list(vars)

    r = Renaming([])
    for a in vars:
        assert allowedVars
        b = random.choice(allowedVars)
        if unique:
            allowedVars.remove(b)
        r.subs.append([a, b])

    return r.applyTo(t), r


def organize(t: Type) -> Intersection:
    match t:
        case Variable(_) as var:
            return Intersection([var])
        case Intersection(types):
            return Intersection([organize(t) for t in types])
        case Arrow(l, r):
            return Intersection([Arrow(l, t) for t in organize(r).types])

    assert False

def isPath(t: Type) -> bool:
    match t:
        case Variable(_):
            return True
        case Arrow(l, r):
            return isPath(r)
        case _:
            return False

def isBasic(c: Constraint):
    match c.left, c.right:
        case Variable(_) | Intersection([]), _:
            return True
        case _, Variable(_) | Intersection([]):
            return True