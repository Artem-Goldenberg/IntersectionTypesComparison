import random
from type import *
from utils import randomRename

collection = list(types.values())

def deepType(depth: int, width: int, varsCount: int) -> tuple[Type, Type, Renaming]:
    vars = [Variable(f"a{i}") for i in range(varsCount)]
    k = 0
    previous = Intersection([random.choice(collection) for _ in range(width)])

    for i in range(depth):
        types: list[Type] = []
        for _ in range(width - 1):
            type = random.choice(collection)
            type, _ = randomRename(type, vars, unique=False)
            types.append(type)
        types.append(Arrow(previous, vars[k]))
        k = (k + 1) % varsCount
        current = Intersection(types)
        previous = current
    
    t = previous
    s, r = randomRename(t)
    return t, s, r


def manyVariables(depth: int, width: int = 7) -> tuple[Type, Type, Renaming]:
    vars = [Variable(f"a{i}") for i in range(width * 2)]
    k = 0
    previous = Intersection([random.choice(collection) for _ in range(width)])

    for i in range(depth):
        types: list[Type] = []
        sub = random.randint(1, 4)
        for _ in range(width - sub):
            type = random.choice(vars)
            types.append(type)
        for _ in range(sub - 1):
            type = random.choice(collection)
            type, _ = randomRename(type, vars, unique=False)
            types.append(type)

        types.append(Arrow(previous, vars[k]))
        k = (k + 1) % len(vars)

        current = Intersection(types)
        previous = current
    
    t = previous
    s, r = randomRename(t)
    return t, s, r
