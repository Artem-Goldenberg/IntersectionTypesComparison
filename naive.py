from model import *
from utils import *

def normalForm(t: Type) -> Type:
    return removeDuplicates(typeSort(t))

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

    # switch comments to choose from bijections
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
