import random
from typing import Callable
from type import *
from utils import randomRename, normalForm
import signal
import time
import numpy as np
from tqdm import tqdm

collection = list(types.values())

def testType(depth: int, width: int, varsCount: int) -> tuple[Type, Type, Renaming]:
    vars = [Variable(f"a{i}") for i in range(varsCount)]
    k = 0
    types: list[Type] = []
    for _ in range(width - 1):
        type = random.choice(collection)
        type, _ = randomRename(type, vars, unique=False)
        types.append(type)
    previous = Intersection(types)

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
    s = shuffled(s)
    return t, s, r


def manyVariables(depth: int, width: int) -> tuple[Type, Type, Renaming]:
    vars = [Variable(f"a{i}") for i in range(width * 2)]
    previous = Intersection([random.choice(vars) for _ in range(width)])

    k = 0
    for _ in range(depth):
        types: list[Type] = [random.choice(vars) for _ in range(width - 1)]
        types.append(Arrow(previous, vars[k]))
        k = (k + 1) % len(vars)
        current = Intersection(types)
        previous = current

    t = previous
    s, r = randomRename(t)
    s = shuffled(s)
    return t, s, r


def shuffled(t: Type) -> Type:
    match t:
        case Variable(_) as a:
            return a
        case Arrow(l, r):
            return Arrow(shuffled(l), shuffled(r))
        case Intersection(types):
            types1 = list(map(shuffled, types))
            random.shuffle(types1)
            return Intersection(types1)
    assert False


# def manyVariables(depth: int, width: int = 7) -> tuple[Type, Type, Renaming]:
#     vars = [Variable(f"a{i}") for i in range(width * 2)]
#     k = 0
#     types: list[Type] = []
#     for _ in range(width - 1):
#         type = random.choice(collection)
#         type, _ = randomRename(type, vars, unique=False)
#         types.append(type)
#     previous = Intersection(types)

#     for i in range(depth):
#         types: list[Type] = []
#         sub = random.randint(1, max(width, 4))
#         for _ in range(width - sub):
#             type = random.choice(vars)
#             types.append(type)
#         for _ in range(sub - 1):
#             type = random.choice(collection)
#             type, _ = randomRename(type, vars, unique=False)
#             types.append(type)

#         types.append(Arrow(previous, vars[k]))
#         k = (k + 1) % len(vars)

#         current = Intersection(types)
#         previous = current
    
#     t = previous
#     s, r = randomRename(t)
#     return t, s, r


def throwTimeout(signum, frame):
    raise TimeoutError


runs = 10
laps = 10
timeout = 1 # in seconds

def assertResult(t, s, r):
    assert normalForm(r.applyTo(t)) == normalForm(s)

def speedTest(
        samples: list[int], 
        algos: list[Callable[[Type, Type], Renaming | None]],
        typeGen: Callable[[int], tuple[Type, Type, Renaming]]
    ):
    signal.signal(signal.SIGALRM, throwTimeout)

    result = np.zeros((len(algos), len(samples), runs), dtype=np.float64)

    didTimeout = [False] * len(algos)
    for i, d in tqdm(enumerate(samples)):
        for j, algo in enumerate(algos):
            if didTimeout[j]: continue
            for run in range(runs):
                t, s, r = typeGen(d)
                avg = 0 # in nanoseconds
                for lap in range(laps):
                    signal.alarm(timeout)
                    try:
                        start = time.perf_counter_ns()
                        res = algo(t, s)
                        end = time.perf_counter_ns()
                        signal.alarm(1000)
                        avg += end - start
                        assertResult(t, s, res)
                    except TimeoutError:
                        print(f"timeout of {j} at {d}")
                        didTimeout[j] = True
                        break
                if didTimeout[j]: break
                avg /= laps
                result[j, i, run] = avg / 1e6
    
    signal.signal(signal.SIGALRM, signal.SIG_IGN)
    
    return result
