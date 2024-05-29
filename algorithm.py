from collections import defaultdict
from itertools import permutations
from typing import Generator
from main import normalForm
from model import *
from utils import *

Solution = dict[Variable, Variable]
AllowedMap = dict[Variable, set[Variable]]
AllowedList = list[tuple[Variable, set[Variable]]]
SizeClassMap = defaultdict[int, list[Type]]

def comparePlain(t: Type, s: Type) -> Renaming | None:
    t = normalForm(t)
    s = normalForm(s)

    solution = solve([Constraint(t, s)], {})
    if solution is None:
        return None
    return Renaming([[a, b] for a, b in solution.items()])


def compareSizeClasses(t: Type, s: Type) -> Renaming | None:
    t = normalForm(t)
    s = normalForm(s)

    solution = solveWithSizeClasses([Constraint(t, s)], {})
    if solution is None:
        return None
    return Renaming([[a, b] for a, b in solution.items()])


def compareConstraintProp(t: Type, s: Type) -> Renaming | None:
    t = normalForm(t)
    s = normalForm(s)

    solution = solveWithConstraintProp([Constraint(t, s)], {})
    if solution is None:
        return None
    return Renaming([[a, b] for a, b in solution.items()])


def compareConstraintPropSizeClasses(t: Type, s: Type) -> Renaming | None:
    t = normalForm(t)
    s = normalForm(s)

    solution = solveWithConstraintPropAndSizeClasses([Constraint(t, s)], {})
    if solution is None:
        return None
    return Renaming([[a, b] for a, b in solution.items()])


def solveWithConstraintPropAndSizeClasses(C: list[Constraint], S: Solution) -> Solution | None:
    if not C:
        return S

    c, *C1 = C
    
    # propagation step
    if isinstance(c, VariableConstraint):
        allowed: dict[Variable, set[Variable]] = {}

        for v in c.left:
            # guaranteed that v was never here before
            if v not in S:
                allowed[v] = set(c.right)

        for varConstr in C1:
            assert isinstance(varConstr, VariableConstraint)
            for v in varConstr.left:
                if v in S:
                    continue
                elif v not in allowed:
                    allowed[v] = set(varConstr.right)
                else:
                    allowed[v].intersection_update(varConstr.right)
        
        allowedList = sorted(allowed.items(), key=lambda item: len(item[1]))
        solution = solveVariableConstraints(allowedList, C) # type: ignore
        if solution is None: return None

        assert len(solution) == len(allowedList)

        S.update({k[0]: v for k, v in zip(allowedList, solution)})
        return S

        
    match c.left, c.right:
        case Variable(_) as a, Variable(_) as b:
            if a not in S:
                S1 = dict(S)
                S1[a] = b
                return solveWithConstraintPropAndSizeClasses(C1, S1)
            elif S[a] == b:
                return solveWithConstraintPropAndSizeClasses(C1, S)
            else:
                return None
        case Arrow(l1, r1), Arrow(l2, r2):
            return solveWithConstraintPropAndSizeClasses([Constraint(l1, l2), Constraint(r1, r2)] + C1, S)
        case Intersection(types1), Intersection(types2):
            if len(types1) != len(types2):
                return None
            if not types1:
                return solveWithConstraintPropAndSizeClasses(C1, S)

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
                
            if sizeClasses1.get(1) is not None:
                varConstr = VariableConstraint(sizeClasses1[1], sizeClasses2[1]) # type: ignore
                del sizeClasses1[1]
                del sizeClasses2[1]
                C1.append(varConstr)
                if not sizeClasses1:
                    return solveWithConstraintPropAndSizeClasses(C1, S)

            def getConstraints(sizes: list[int]) \
            -> Generator[list[Constraint], None, None]:
                if not sizes: 
                    yield []
                    return
                size, *sizes = sizes
                class1 = sizeClasses1[size]
                for p in permutations(sizeClasses2[size]):
                    for constraints in getConstraints(sizes):
                        yield [Constraint(t1, t2) for t1, t2 in zip(class1, p)] \
                            + constraints

            for constraints in getConstraints(list(sizeClasses1.keys())):
                S1 = solveWithConstraintPropAndSizeClasses(constraints + C1, S)
                if S1 is not None:
                    return S1

            return None

@dataclass
class VariableConstraint(Constraint):
    left: list[Variable]
    right: list[Variable]

    def __str__(self):
        strLeft = ", ".join(map(str, self.left))
        strRight = ", ".join(map(str, self.right))
        return f"[{strLeft}] = [{strRight}]"


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


def solveWithConstraintProp(C: list[Constraint], S: Solution) -> Solution | None:
    if not C:
        return S

    c, *C1 = C
    
    # propagation step
    if isinstance(c, VariableConstraint):
        allowed: dict[Variable, set[Variable]] = {}

        for v in c.left:
            # guaranteed that v was never here before
            if v not in S:
                allowed[v] = set(c.right)

        for varConstr in C1:
            assert isinstance(varConstr, VariableConstraint)
            for v in varConstr.left:
                if v in S:
                    continue
                elif v not in allowed:
                    allowed[v] = set(varConstr.right)
                else:
                    allowed[v].intersection_update(varConstr.right)
        
        allowedList = sorted(allowed.items(), key=lambda item: len(item[1]))
        solution = solveVariableConstraints(allowedList, C) # type: ignore
        if solution is None: return None

        assert len(solution) == len(allowedList)

        return {k[0]: v for k, v in zip(allowedList, solution)}

        
    match c.left, c.right:
        case Variable(_) as a, Variable(_) as b:
            # for c in C1:
            #     if isinstance(c, VariableConstraint):
            #         if a in c.left:
            #             try:
            #                 c.right.remove(b)
            #             except ValueError:
            #                 return None
            #             c.left.remove(a)
            #     else:                


            # return solveWithConstraintProp(C1 + [VariableConstraint([a], [b])])
            if a not in S:
                S1 = dict(S)
                S1[a] = b
                return solveWithConstraintProp(C1, S1)
            elif S[a] == b:
                return solveWithConstraintProp(C1, S)
            else:
                return None
        case Arrow(l1, r1), Arrow(l2, r2):
            return solveWithConstraintProp([Constraint(l1, l2), Constraint(r1, r2)] + C1, S)
        case Intersection(types1), Intersection(types2):
            if len(types1) != len(types2):
                return None
            if not types1:
                return solveWithConstraintProp(C1, S)

            varBound = 0
            for v1, v2 in zip(types1, types2):
                if v1 is Variable and v2 is Variable:
                    varBound += 1
                elif v1 is not Variable and v2 is not Variable:
                    break
                else:
                    return None
            
            if varBound != 0:
                varConstr = VariableConstraint(types1[:varBound], types2[:varBound]) # type: ignore
                constr = [Constraint(
                    Intersection(types1[varBound:]),
                    Intersection(types2[varBound:])
                )] if varBound != len(types1) else []
                return solveWithConstraintProp(constr + C1 + [varConstr], S)

            for p in permutations(types2):
                S1 = solveWithConstraintProp([Constraint(t1, t2) for t1, t2 in zip(types1, p)] + C1, S)
                if S1 is not None:
                    return S1

            return None


def solveWithSizeClasses(C: list[Constraint], S: Solution) -> Solution | None:
    if not C:
        return S
    
    c, *C1 = C

    match c.left, c.right:
        case Variable(_) as a, Variable(_) as b:
            if a not in S:
                S1 = dict(S)
                S1[a] = b
                return solveWithSizeClasses(C1, S1)
            elif S[a] == b:
                return solveWithSizeClasses(C1, S)
            else:
                return None
        case Arrow(l1, r1), Arrow(l2, r2):
            return solveWithSizeClasses([Constraint(l1, l2), Constraint(r1, r2)] + C1, S)
        case Intersection(types1), Intersection(types2):
            if len(types1) != len(types2):
                return None
            if not types1:
                return solveWithSizeClasses(C1, S)

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

            def getConstraints(sizes: list[int]) \
            -> Generator[list[Constraint], None, None]:
                if not sizes: 
                    yield []
                    return
                size, *sizes = sizes
                class1 = sizeClasses1[size]
                for p in permutations(sizeClasses2[size]):
                    for constraints in getConstraints(sizes):
                        yield [Constraint(t1, t2) for t1, t2 in zip(class1, p)] \
                            + constraints

            for constraints in getConstraints(list(sizeClasses1.keys())):
                S1 = solveWithSizeClasses(constraints + C1, S)
                if S1 is not None:
                    return S1

            return None


def solve(C: list[Constraint], S: Solution) -> Solution | None:
    if not C:
        return S
    
    c, *C1 = C

    match c.left, c.right:
        case Variable(_) as a, Variable(_) as b:
            if a not in S:
                S1 = dict(S)
                S1[a] = b
                return solve(C1, S1)
            elif S[a] == b:
                return solve(C1, S)
            else:
                return None
        case Arrow(l1, r1), Arrow(l2, r2):
            return solve([Constraint(l1, l2), Constraint(r1, r2)] + C1, S)
        case Intersection(types1), Intersection(types2):
            if len(types1) != len(types2):
                return None
            if not types1:
                return solve(C1, S)

            for p in permutations(types2):
                S1 = solve([Constraint(t1, t2) for t1, t2 in zip(types1, p)] + C1, S)
                if S1 is not None:
                    return S1

            return None
