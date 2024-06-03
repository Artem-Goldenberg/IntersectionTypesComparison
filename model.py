from dataclasses import dataclass
from abc import ABC, abstractmethod
from functools import total_ordering

@total_ordering
@dataclass(frozen=True)
class Type(ABC):
    # @abstractmethod
    # def getSymbols(self) -> set[str]: ...
    @abstractmethod
    def __str__() -> str: ...

    def __lt__(self, s: 'Type') -> bool:
        match self, s:
            case Variable(a), Variable(b):
                return a < b
            case Variable(_), _:
                return True
            case Arrow(l1, r1), Arrow(l2, r2):
                return (l1, r1) < (l2, r2)
            case Arrow(_, _), Intersection(_):
                return True
            case Intersection(types1), Intersection(types2):
                # keyFunc = cmp_to_key(makeCmp(less))
                # types1.sort()
                # types2.sort()
                return types1 < types2
            case _, _:
                return False


@dataclass(frozen=True)
class Variable(Type):
    name: str

    def __str__(self):
        return self.name

@dataclass(frozen=True)
class Intersection(Type):
    types: list[Type]

    def __str__(self):
        if not self.types:
            return "ω"
        strs = []
        for t in self.types:
            if isinstance(t, Variable):
                strs.append(f"{t}")
            else:
                strs.append(f"({t})")
        return r" /\ ".join(strs)

@dataclass(frozen=True)
class Arrow(Type):
    left: Type
    right: Type

    def __str__(self):
        strLeft = f"({self.left})"
        strRight = f"{self.right}"
        match self.left:
            case Variable(_) as a:
                strLeft = a
            case Intersection([Variable(a)]):
                strLeft = a
            case Intersection([]):
                strLeft = self.left
        # match self.right:
        #     case Variable(_) as a:
        #         strRight = a
        #     case Intersection([Variable(a)]):
        #         strRight = a
        return f"{strLeft} -> {strRight}"

@dataclass
class Constraint:
    left: Type
    right: Type

    def __str__(self):
        strLeft = f"({self.left})"
        strRight = f"({self.right})"
        match self.left:
            case Intersection([Variable(a)]):
                strLeft = a
        match self.right:
            case Intersection([Variable(a)]):
                strRight = a
        return f"{strLeft} = {strRight}"

@dataclass
class VariableConstraint(Constraint):
    left: set[Variable]
    right: set[Variable]

    def __str__(self):
        strLeft = ", ".join(map(str, self.left))
        strRight = ", ".join(map(str, self.right))
        return f"[{strLeft}] = [{strRight}]"

@dataclass()
class Renaming:
    # subs: dict[Variable, Variable]
    subs: list[list[Variable]]

    def inverse(self, b: Variable) -> Variable | None:
        for (k, v) in self.subs:
            if b == v: return k
        return None

    def get(self, a: Variable, default: Variable | None = None) -> Variable | None:
        for (k, v) in self.subs:
            if a == k: return v
        return default

    def __eq__(self, other: 'Renaming') -> bool:
        for k, v in self.subs:
            if other.get(k) != v:
                return False
        return len(self.subs) == len(other.subs)

    def applyTo(self, t: Type) -> Type:
        match t:
            case Variable(_) as a:
                return self.get(a, default=a) # type: ignore
            case Intersection(types):
                return Intersection([self.applyTo(t) for t in types])
            case Arrow(l, r):
                return Arrow(self.applyTo(l), self.applyTo(r))
            case _:
                return t

    def __str__(self) -> str:
        return "{" + r", ".join([f"{k} -> {v}" for k, v in sorted(self.subs)]) + "}"
