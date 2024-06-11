from collections import defaultdict
from itertools import permutations
from typing import Generator
from naive import normalForm
from model import *
from utils import *

Solution = dict[Variable, Variable]
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
                except ValueError: return False
                c.left.remove(a)
    return True

@dataclass
class Occurrence:
    var: Variable
    used: bool = False
    # constraint: VariableConstraint

@dataclass
class AllowedVariable:
    var: Variable
    evidence: list[Occurrence]

    def __eq__(self, other: 'AllowedVariable') -> bool:
        return self.var == other.var

    def __hash__(self) -> int:
        return hash(self.var)


AllowedMap = dict[Variable, set[Variable]]
AllowedList = list[tuple[Variable, set[AllowedVariable]]]


def propagationCase(c: VariableConstraint, C: list[Constraint], S: Solution) -> Solution | None:
    allowed: dict[Variable, set[AllowedVariable]] = {}

    if not applySolution([c] + C, S): #type: ignore
        return None
    
    occurrences: list[list[Occurrence]] = []
    # constraints: list[tuple[set[Variable], set[AllowedVariable]]] = []
    for constr in c, *C:
        assert isinstance(constr, VariableConstraint)
        occurrences.append([Occurrence(var) for var in constr.right])

    # for v in c.left:
    #     # guaranteed that v was never here before
    #     allowed[v] = set(AllowedVariable(var, ) for var in c.right)

    for constr, occs in zip([c] + C, occurrences):
        assert isinstance(constr, VariableConstraint)
        for v in constr.left:
            if v not in allowed:
                allowed[v] = set(AllowedVariable(occ.var, [occ]) for occ in occs)
            else:
                # find intersection
                for allowedVar in allowed[v].copy():
                    if allowedVar.var not in constr.right:
                        allowed[v].remove(allowedVar)
                    else:
                        for occ in occs:
                            if occ.var == allowedVar.var:
                                allowedVar.evidence.append(occ)
                                break
                        else: assert False

                # allowed[v].intersection(varConstr.right)
                # allowed[v].intersection_update(varConstr.right)
    
    allowedList = sorted(allowed.items(), key=lambda item: len(item[1]))
    solution = solveVariableConstraints(allowedList) # type: ignore
    if solution is None: return None

    assert len(solution) == len(allowedList)

    S.update({k[0]: v for k, v in zip(allowedList, solution)})
    return S


def solveVariableConstraints(allowed: AllowedList) -> list[Variable] | None:
    if not allowed:
        return []
    
    (a, allowedVars), *allowed = allowed

    if not allowedVars:
        # conflicting constraints on v
        return None

    def isTaken(allowedVar: AllowedVariable) -> bool:
        for occ in allowedVar.evidence:
            if occ.used:
                return True
        return False
    
    for allowedVar in allowedVars:
        if isTaken(allowedVar):
            continue

        for occ in allowedVar.evidence:
            occ.used = True

        solution = solveVariableConstraints(allowed)
        if solution is not None:
            return [allowedVar.var] + solution

        for occ in allowedVar.evidence:
            occ.used = False
    
    return None


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
        if isinstance(v1, Variable) and isinstance(v2, Variable):
            varBound += 1
        elif not isinstance(v1, Variable) and not isinstance(v2, Variable):
            return varBound
        else:
            return None
    return varBound


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
