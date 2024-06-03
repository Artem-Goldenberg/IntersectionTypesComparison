from collections import defaultdict
from itertools import permutations
from typing import Generator
from naive import normalForm
from model import *
from utils import *

Solution = dict[Variable, Variable]
AllowedMap = dict[Variable, set[Variable]]
AllowedList = list[tuple[Variable, set[Variable]]]
SizeClassMap = defaultdict[int, list[Type]]

def comparePlain(t: Type, s: Type) -> Renaming | None:
    t = normalForm(t)
    s = normalForm(s)

    solution = PlainSolve([Constraint(t, s)], {})
    if solution is None:
        return None
    return Renaming([[a, b] for a, b in solution.items()])


def compareSizeCount(t: Type, s: Type) -> Renaming | None:
    t = normalForm(t)
    s = normalForm(s)

    solution = SizeCountSolve([Constraint(t, s)], {})
    if solution is None:
        return None
    return Renaming([[a, b] for a, b in solution.items()])


def compareConstrProp(t: Type, s: Type) -> Renaming | None:
    t = normalForm(t)
    s = normalForm(s)

    solution = ConstrPropSolve([Constraint(t, s)], {})
    if solution is None:
        return None
    return Renaming([[a, b] for a, b in solution.items()])


def compareConstrPropSizeCount(t: Type, s: Type) -> Renaming | None:
    t = normalForm(t)
    s = normalForm(s)

    solution = SizeCountConstrPropSolve([Constraint(t, s)], {})
    if solution is None:
        return None
    return Renaming([[a, b] for a, b in solution.items()])


def applySolution(C: list[VariableConstraint], S: Solution) -> bool:
    for c in C:
        for a in list(c.left):
            if a in S:
                try: c.right.remove(S[a])
                except KeyError: return False
                c.left.remove(a)
    return True


def propagationCase(c: VariableConstraint, C: list[Constraint], S: Solution) -> Solution | None:
    allowed: dict[Variable, set[Variable]] = {}

    if not applySolution(C, S): #type: ignore
        return None

    for v in c.left:
        # guaranteed that v was never here before
        allowed[v] = set(c.right)

    for varConstr in C:
        assert isinstance(varConstr, VariableConstraint)
        for v in varConstr.left:
            if v not in allowed:
                allowed[v] = set(varConstr.right)
            else:
                allowed[v].intersection_update(varConstr.right)
    
    allowedList = sorted(allowed.items(), key=lambda item: len(item[1]))
    solution = solveVariableConstraints(allowedList, C) # type: ignore
    if solution is None: return None

    assert len(solution) == len(allowedList)

    S.update({k[0]: v for k, v in zip(allowedList, solution)})
    return S


def SizeCountConstrPropSolve(C: list[Constraint], S: Solution) -> Solution | None:
    if not C:
        return S

    c, *C1 = C
    
    # propagation step
    if isinstance(c, VariableConstraint):
        return propagationCase(c, C1, S)
        
    match c.left, c.right:
        case Variable(_) as a, Variable(_) as b:
            if a not in S:
                S1 = dict(S)
                S1[a] = b
                return SizeCountConstrPropSolve(C1, S1)
            elif S[a] == b:
                return SizeCountConstrPropSolve(C1, S)
            else:
                return None
        case Arrow(l1, r1), Arrow(l2, r2):
            return SizeCountConstrPropSolve([Constraint(l1, l2), Constraint(r1, r2)] + C1, S)
        case Intersection(types1), Intersection(types2):
            if len(types1) != len(types2):
                return None
            if not types1:
                return SizeCountConstrPropSolve(C1, S)

            varBound = getVarBound(types1, types2)
            if varBound is None: return None
            
            if varBound != 0:
                varConstr = VariableConstraint(types1[:varBound], types2[:varBound]) # type: ignore
                C1.append(varConstr)
                if varBound == len(types1):
                    return SizeCountConstrPropSolve(C1, S)
                types1 = types1[varBound:]
                types2 = types2[varBound:]
            
            gen = sizeSplit(types1, types2)
            if gen is None: return None

            for constraints in gen:
                S1 = SizeCountConstrPropSolve(constraints + C1, S)
                if S1 is not None:
                    return S1

            return None


def solveVariableConstraints(allowed: AllowedList, C: list[VariableConstraint]) -> list[Variable] | None:
    if not allowed:
        return []
    
    (a, vars), *allowed = allowed

    if not vars:
        # conflicting constraints on v
        return None
    
    for var in vars:
        for c in C:
            if a in c.left:
                for v, allowedVars in allowed:
                    if v in c.left:
                        allowedVars.discard(var)

        solution = solveVariableConstraints(allowed, C)
        if solution is not None:
            return solution + [var]

        for c in C:
            if a in c.left:
                for v, allowedVars in allowed:
                    if v in c.left:
                        allowedVars.add(var)
    
    return None


def ConstrPropSolve(C: list[Constraint], S: Solution) -> Solution | None:
    if not C:
        return S

    c, *C1 = C
    
    # propagation step
    if isinstance(c, VariableConstraint):
       return propagationCase(c, C1, S)
        
    match c.left, c.right:
        case Variable(_) as a, Variable(_) as b:
            if a not in S:
                S1 = dict(S)
                S1[a] = b
                return ConstrPropSolve(C1, S1)
            elif S[a] == b:
                return ConstrPropSolve(C1, S)
            else:
                return None
        case Arrow(l1, r1), Arrow(l2, r2):
            return ConstrPropSolve([Constraint(l1, l2), Constraint(r1, r2)] + C1, S)
        case Intersection(types1), Intersection(types2):
            if len(types1) != len(types2):
                return None
            if not types1:
                return ConstrPropSolve(C1, S)

            varBound = getVarBound(types1, types2)
            if varBound is None: return None
            
            if varBound != 0:
                varConstr = VariableConstraint(types1[:varBound], types2[:varBound]) # type: ignore
                C1.append(varConstr)
                if varBound == len(types1):
                    return ConstrPropSolve(C1, S)
                types1 = types1[varBound:]
                types2 = types2[varBound:]
                # constr = [Constraint(
                #     Intersection(types1[varBound:]),
                #     Intersection(types2[varBound:])
                # )] if varBound != len(types1) else []
                # return solveWithConstraintProp(constr + C1 + [varConstr], S)

            for p in permutations(types2):
                S1 = ConstrPropSolve([Constraint(t1, t2) for t1, t2 in zip(types1, p)] + C1, S)
                if S1 is not None:
                    return S1

            return None

def getVarBound(types1: list[Type], types2: list[Type]) -> int | None:
    varBound = 0
    for v1, v2 in zip(types1, types2):
        if v1 is Variable and v2 is Variable:
            varBound += 1
        elif v1 is not Variable and v2 is not Variable:
            return varBound
        else:
            return None


def sizeSplit(types1: list[Type], types2: list[Type]) -> Generator[list[Constraint], None, None]:
    sizeClasses1: SizeClassMap = defaultdict(list)
    for t in types1:
        sizeClasses1[typeSize(t)].append(t)
    sizeClasses2: SizeClassMap = defaultdict(list)
    for t in types2:
        sizeClasses2[typeSize(t)].append(t)

    # first big divider
    if sizeClasses1.keys() != sizeClasses2.keys():
        return None
    
    # second big divider
    for s, types in sizeClasses1.items():
        if len(types) != len(sizeClasses2[s]):
            return None

    def getConstraints(sizes: list[int]) -> Generator[list[Constraint], None, None]:
        if not sizes: 
            yield []
            return
        size, *sizes = sizes
        class1 = sizeClasses1[size]
        for p in permutations(sizeClasses2[size]):
            for constraints in getConstraints(sizes):
                yield [Constraint(t1, t2) for t1, t2 in zip(class1, p)] \
                    + constraints
    
    yield from getConstraints(list(sizeClasses1.keys()))


def SizeCountSolve(C: list[Constraint], S: Solution) -> Solution | None:
    if not C:
        return S
    
    c, *C1 = C

    match c.left, c.right:
        case Variable(_) as a, Variable(_) as b:
            if a not in S:
                S1 = dict(S)
                S1[a] = b
                return SizeCountSolve(C1, S1)
            elif S[a] == b:
                return SizeCountSolve(C1, S)
            else:
                return None
        case Arrow(l1, r1), Arrow(l2, r2):
            return SizeCountSolve([Constraint(l1, l2), Constraint(r1, r2)] + C1, S)
        case Intersection(types1), Intersection(types2):
            if len(types1) != len(types2):
                return None
            if not types1:
                return SizeCountSolve(C1, S)

            gen = sizeSplit(types1, types2)
            if gen is None: return None

            for constraints in gen:
                S1 = SizeCountSolve(constraints + C1, S)
                if S1 is not None:
                    return S1

            return None


def PlainSolve(C: list[Constraint], S: Solution) -> Solution | None:
    if not C:
        return S
    
    c, *C1 = C

    match c.left, c.right:
        case Variable(_) as a, Variable(_) as b:
            if a not in S:
                S1 = dict(S)
                S1[a] = b
                return PlainSolve(C1, S1)
            elif S[a] == b:
                return PlainSolve(C1, S)
            else:
                return None
        case Arrow(l1, r1), Arrow(l2, r2):
            return PlainSolve([Constraint(l1, l2), Constraint(r1, r2)] + C1, S)
        case Intersection(types1), Intersection(types2):
            if len(types1) != len(types2):
                return None
            if not types1:
                return PlainSolve(C1, S)

            for p in permutations(types2):
                S1 = PlainSolve([Constraint(t1, t2) for t1, t2 in zip(types1, p)] + C1, S)
                if S1 is not None:
                    return S1

            return None
