from yalog import var, kbmeta

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

    # Definite clauses
    grandfather(X, Y) <= \
        father(X, Z) & father(Z, Y)
    parent(X, Y) <= \
        father(X, Y) |\
        mother(X, Y)
    sibling(X, Y) <= \
        parent(Z, X) & parent(Z, Y) & (X != Y)

    ancester(X, Y) <= father(X, Y)
    ancester(X, Y) <= father(X, Z) & ancester(Z, Y)


from pprint import pprint

# q = kb.sibling(var.X, var.Y)
# q = kb.sibling(var.a_sib, 'a')
q = kb.sibling(var.x, var.y)
pprint(list(q))

q = kb.ancester(var.W, 'a')
pprint(list(q))
