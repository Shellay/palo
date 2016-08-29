from yalog import kbmeta, var, new_vars

class kb(metaclass=kbmeta):

    # Facts
    father('ooopa', 'opa')
    father('opa', 'ucl')
    father('opa', 'pa')
    mother('oma', 'pa')
    father('pa', 'a')
    father('pa', 'b')
    mother('mum', 'a')
    mother('mum', 'b')
    mother('mum', 1)

    # Definite clauses
    grandfather(X, Y) <= [
        father(X, Z), father(Z, Y)
    ]
    parent(X, Y) <= father(X, Y)
    parent(X, Y) <= mother(X, Y)

    sibling(X, Y) <= [
        parent(Z, X), parent(Z, Y), not_eq(X, Y)
        # Applying not_eq to yet instantiated variables lead to failure.
        # This means, UNSAFE query is hereby directly rejected.
        # i.e. 
        # not_eq(X, Y), parent(Z, X), parent(Z, Y)
    ]

    ancester(X, Y) <= father(X, Y)
    ancester(X, Y) <= [
        father(X, Z), ancester(Z, Y)
    ]

    # fac(0, F) <= eq(1, F)
    # fac(N, F) <= [fac(sub(N, 1), F_1), eq(mul(F_1, N), F)]


from pprint import pprint

pprint(kb)

# q = kb.sibling(var.X, var.Y)
# q = kb.sibling(var.a_sib, 'a')
print('=== siblings ===')
q = kb.sibling(var.x, var.y)
# q = kb.sibling(var.x, 'a')
pprint(list(q))

print()
print('=== ancesters ===')
q = kb.ancester(var.W, 'a')
pprint(list(q))


print()
with new_vars(3) as (X, Y, Z):
    # print(X, Y, Z)
    pass

