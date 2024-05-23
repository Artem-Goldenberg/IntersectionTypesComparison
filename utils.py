from model import *
from functools import cmp_to_key, reduce

def typeSort(t: Type) -> Type:
    match t:
        case Variable(_) as a: 
            return a
        case Intersection(types):
            return Intersection(sorted(types))
        case Arrow(l, r):
            return Arrow(typeSort(l), typeSort(r))
    assert False

def getVars(t: Type) -> set[Variable]:
    match t:
        case Variable(_):
            return {t}
        case Arrow(l, r):
            return getVars(l).union(getVars(r))
        case Intersection(types):
            return reduce(lambda vs1, vs2: vs1.union(vs2), map(getVars, types))
    assert False
