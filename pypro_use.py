from pypro import KBMan, NotEq, scm, var, Assert, Func, Eq


k = KBMan()
q = k.query

k.father('opa', 'pap')
k.father('pap', 'a')
k.mother('mum', 'a')
k.father('pap', 'b')
k.mother('mum', 'b')

x, y, z = scm(3)

k.sibling(x, y) <= (
    k.father(z, x) &
    k.father(z, y) &
    NotEq(x, y)
)

k.ancester(x, y) <= k.father(x, y)
k.ancester(x, y) <= k.father(x, z) & k.ancester(z, y)

print(k._kb)

r = q.sibling(var.x, var.y)
print(list(r))

r = q.ancester(var.x, var.y)
print(list(r))

import operator as op
k.factorial(0, 1)
k.factorial(x, y) <= (
    Assert(Func(op.ge, x, 0)) &
    k.factorial(Func(op.sub, x, 1), z) &
    Eq(y, Func(op.mul, x, z))
)

r = q.factorial(4, var.w)
# r = q.factorial(4)
print(list(r))
