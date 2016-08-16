from yalog import var, kbmeta

class kb(metaclass=kbmeta):

    # Facts
    father['opa', 'pa']
    mother['oma', 'pa']
    father['pa', 'a']
    father['pa', 'b']
    mother['mum', 'a']
    mother['mum', 'b']
    not_eq['a', 'b']
    not_eq['b', 'a']

    # Horn clauses
    grandfather[X, Y] = father[X, Z], father[Z, Y]
    parent[X, Y] = father[X, Y]
    parent[X, Y] = mother[X, Y]
    sibling[X, Y] = parent[Z, X], parent[Z, Y], not_eq[X, Y]

    # # How to implement implicit equality?
    # sibling[X, Y] = parent[Z, X], parent[Z, Y]


from pprint import pprint

u = next(kb.sibling[var.X, 'b'])
u1 = {var.X: 'a'}
assert u == u1

pprint([*kb.sibling['a', var.X]])
pprint([*kb.sibling['b', var.X]])
pprint([*kb.sibling[var.X, var.Y]])
