from model import *

a = Variable("a") #0
b = Variable("b") #1
c = Variable("c") #2
d = Variable("d") #3
e = Variable("e") #4
f = Variable("f") #5
g = Variable("g") #6

def fo(a, b):
    if isinstance(a, list):
        left = Intersection(a)
    else: 
        left = Intersection([a])
    if isinstance(b, list):
        right = Intersection(b)
    else:
        right = Intersection([b])
    return Arrow(left, right)
    
def typify(t) -> Type:
    match t:
        case tuple((a, b)):
            return Arrow(typify(a), typify(b))
        case list([*types]):
            return Intersection([typify(t) for t in types])
        case tuple((a, b, *c)):
            return Arrow(typify(a), typify((b, *c)))
        case _:
            return t

om = Intersection([])

types = dict(
top = Arrow(a, a),
one = Arrow(Arrow(a, b), Arrow(a, b)),
two = Arrow(
    Intersection([Arrow(b, c), Arrow(a, b)]),
    Arrow(a, c)
),
three = Arrow(
    Intersection([Arrow(c, d), Arrow(b, c), Arrow(a, b)]),
    Arrow(a, d)
),
omega1 = fo(
    [fo(a, b), a], 
    b
),
omega2 = fo(
    [fo(a, fo(b, c)), a, b], c
),
omega3 = typify((
    [(b, c), (a, b), a], c
)),
test1 = typify((
    (a, (a, b), b)
)),
test2 = typify((
    [(b, c), a], (a, b), c
)),
test3 = typify((
    [(a, b, c), b], a, c
)),
test4 = typify((
    ((a, a), b), b
)),
test5 = typify((
    [((om, b), c), ((a, a), b)], c
)),
test6 = typify((
    [((a, b), c), ((om, a), b)], c 
)),
kcomb = typify((
    a, om, a
)),
kastcomb = typify((
    om, a, a
)),
ccomb = typify((
    (a, b, c), b, a, c
)),
bcomb = typify((
    (b, c), (a, b), a, c
)),
scomb = typify((
    (a, c, d), (b, c), [a, b], d
)),
sscomb = typify((
    (b, c, d), [(a, d, e), b], [a, c], e
)),
ssscomb = typify((
    [(a, b, f, g), (c, d)], 
    [a, (d, e, f), c],
    [b, e],
    g
)),
ucomb = typify((
    (a, e, f), (b, d, e), (c, d), [a, b, c], f
)),
diagP = typify((
    [(a, b), (c, d)], [a, c], (b, d, e), e
)),
zero = typify((
    om, a, a
))
)
