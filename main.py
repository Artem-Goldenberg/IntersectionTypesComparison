from model import *

# def typeSort(t: Type) -> Type:
#     match t:
#         case Variable(_) as var:


def organize(t: Type) -> Intersection:
    match t:
        case Variable(_) as var:
            return Intersection([var])
        case Intersection(types):
            return Intersection([organize(t) for t in types])
        case Arrow(l, r):
            return Intersection([Arrow(l, t) for t in organize(r).types])

    assert False

# def reduce(t: Type) -> Type:
#     match t:
#         case Intersection(types):
#             return Intersection(list(filter(lambda t: t != Omega(), map(reduce, types))))
#         case Arrow(l, r):
#             l = reduce(l)
#             r = reduce(r)
#             if r == Omega(): return Omega()
#             return Arrow(l, r)
#         case _:
#             return t

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

    return Renaming({})

def solve(constraints: list[Constraint]) -> Renaming:
    return Renaming({})


def expand(t: Type) -> Type: ...
def removeDuplicates(t: Type) -> Type: ...

def naiveComparison(t: Type, s: Type) -> Renaming | None:
    
