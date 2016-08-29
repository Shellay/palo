from collections import namedtuple, deque
from collections import defaultdict as ddict

## =========================
##      Data Structure
## =========================

Var = namedtuple('Var', 'name')
Var.__repr__ = lambda s: s.name

Cpd = namedtuple('Cpd', 'op args')
Cpd.__repr__ = lambda s: '{}{}'.format(s.op, tuple(s.args))

Rule = namedtuple('Rule', 'csqt prms')
Rule.__repr__ = lambda s: '{{{} <= {}}}'.format(s.csqt, ', '.join(map(repr, s.prms)))


class KB(object):

    class Query(object):
        def __init__(self, kb, op):
            self.kb = kb
            self.op = op
        def __call__(self, *args):
            qc = Cpd(self.op, args)
            yield from self.kb._ask(qc)

    def __init__(self):
        self._facts = ddict(list)
        self._rules = ddict(list)

    def __repr__(self):
        from pprint import pformat
        return pformat((self._facts, self._rules))

    def __getitem__(self, gname):
        if gname in self._facts:
            return self._facts[gname]
        elif gname in self._rules:
            return self._rules[gname]
        else:
            raise KeyError('No such fact/rule.')

    def __getattr__(self, k):
        if k in self.__dict__:
            return self.__dict__[k]
        elif k in self._facts or k in self._rules:
            return self._query(k)
        else:
            raise AttributeError('No such attribute {}.'.format(repr(k)))

    def _query(self, op):
        return KB.Query(self, op)

    def _ask(self):
        raise NotImplementedError('Needing algorithm for answering.')

    def _add_attr(self, k, v):
        setattr(self, k, v)
    def _add_fact(self, fact):
        name = fact.op
        self._facts[name].append(fact)
    def _add_rule(self, rule):
        name = rule[0].op
        self._rules[name].append(rule)

    def _has_fact(self, goal):
        return goal.op in self._facts
    def _has_rule(self, goal):
        return goal.op in self._rules


# Methods

def vars_from(q):
    if type(q) == Var:
        yield q
    elif type(q) == Cpd:
        for m in map(vars_from, q.args):
            yield from m
    elif type(q) in (tuple, list):
        for vs in map(vars_from, q):
            yield from vs
    elif type(q) == Rule:
        yield from vars_from(q.csqt)
        yield from vars_from(q.prms)

def subst(u, e):
    if type(e) == Var:
        if e in u: return u[e]
        else: return e
    elif type(e) == Cpd:
        return Cpd(e.op, tuple(subst(u, a) for a in e.args))
    elif type(e) in (tuple, list):
        return tuple(subst(u, x) for x in e)
    elif type(e) == Rule:
        return Rule(subst(u, e.csqt), subst(u, e.prms))
    else:
        return e


from itertools import count

std_ctr = count()
def stand_apart(rule):
    vs = set(vars_from(rule))
    u = {}
    for i, v in zip(std_ctr, vs):
        u[v] = Var('{}_{}'.format(v.name, i))
    return subst(u, rule)

def stand_reset():
    std_ctr = count()


## =========================
##       Unification
## =========================

FAIL = namedtuple('Fail', '')()

def fails(u):
    return u == FAIL

def unify(x, y, t={}):
    if fails(t):
        return FAIL
    elif x == y:
        return t
    elif type(x) == Var:
        return unify_var(x, y, t)
    elif type(y) == Var:
        return unify_var(y, x, t)
    elif type(x) == type(y) == Cpd:
        t1 = unify(x.op, y.op, t)
        return unify(x.args, y.args, t1)
    elif type(x) == type(y) == tuple:
        for x1, y1 in zip(x, y):
            t = unify(x1, y1, t)
            if fails(t): return FAIL
        return t
    else:
        return FAIL

def unify_var(v, x, t={}):
    if fails(t):
        return FAIL
    elif occur_detect(v, x):
        return FAIL
    elif v in t:
        return unify(t[v], x, t)
    elif x in t:
        return unify(v, t[x], t)
    else:
        return {**t, v: x}

def occur_detect(v, z):
    if type(z) == Var:
        return v == z
    elif type(z) == Cpd:
        return any(occur_detect(v, z) for z in z.args)
    else:
        return False


## =========================
##       Algorithms
## =========================

def bc_ask(kb, query):
    stand_reset()
    qvs = set(vars_from(query))
    for u in bc_1(kb, query, {}):
        # Hide intermediate variables
        # yield u
        yield {k: u[k] for k in u if k in qvs}

def bc_1(kb, goal, u):
    # if goal.op == 'not_':
    #     yield from bc_not(kb, goal.args[0], u)
    if goal.op == 'eq':
        yield from bc_eq(kb, goal.args[0], goal.args[1], u)
    elif goal.op == 'not_eq':
        yield from bc_not_eq(kb, goal.args[0], goal.args[1], u)
    else:
        yield from bc_or(kb, goal, u)

def bc_eq(kb, a1, a2, u):
    u1 = unify(a1, a2, u)
    if not fails(u1):
        yield u1

def bc_not(kb, goal, u):
    """Negation-as-failure. This is a common limitation of prolog-like
    systems.

    May view resources like
    `http://www.cs.toronto.edu/~ajuma/326f08/20Prolog5.pdf` to check
    the details.

    """
    for u1 in bc_1(kb, goal, u):
        # Loop entered -> goal proved -> neg-fail
        yield FAIL

def bc_not_eq(kb, a1, a2, u):
    """Specialization of negation-as-failure."""
    # Directly report non-instantiation.
    while type(a1) is Var:
        if a1 not in u:
            assert 0, 'No instance for {}.'.format(a1)
        a1 = u[a1]
    while type(a2) is Var:
        if a2 not in u:
            assert 0, 'No instance for {}.'.format(a2)
        a2 = u[a2]
    if a1 != a2:
        yield u
    # # Alternatively, can't prove -> failure.
    # if fails(unify(a1, a2, u)):
    #     yield u

def bc_or(kb, goal, u):
    if kb._has_fact(goal):
        for fact in kb[goal.op]:
            u1 = unify(fact, goal, u)
            if not fails(u1):
                yield u1
    elif kb._has_rule(goal):
        # for c, ps in kb[goal.op]:
            # if not fails(unify(csqt, goal)):
            #     csqt, prms = stand_apart((csqt, prms))
            #     u1 = unify(csqt, goal, u)
            #     for u2 in bc_and(kb, prms, u1):
            #         yield u2
        for rule in kb[goal.op]:
            csqt, prms = stand_apart(rule)
            u1 = unify(csqt, goal, u)
            for u2 in bc_and(kb, prms, u1):
                yield u2
    else:
        raise KeyError('No defined rules match {}'.format(repr(goal)))

def bc_and(kb, goals, u):
    if fails(u):
        pass
    elif not goals:
        yield u
    else:
        for u1 in bc_1(kb, subst(u, goals[0]), u):
            for u2 in bc_and(kb, goals[1:], u1):
                yield u2


KB._ask = bc_ask


## =========================
##        Easy Use
## =========================

class _V(object):
    def __getattr__(self, k):
        return Var(k)

var = _V()

class _NV(object):
    def __init__(self, n):
        self.n = n
    def __enter__(self):
        for i in range(self.n):
            yield Var('#_{}'.format(i))
    def __exit__(self, *a, **kw):
        pass

new_vars = _NV
        

class Term(object):

    def __init__(self, name):
        self.name = name
        self.args = []
    def __repr__(self):
        return '{}{}'.format(self.name, self.args or '')

    def __call__(self, *args):
        self.args = []
        for arg in args:
            if type(arg) in (Term, Var):
                self.args.append(Var(arg.name))
            else:
                self.args.append(arg)
        if all(type(x) != Var for x in self.args):
            kbmeta.kb._add_fact(self.to_cpd())
        return self

    def __le__(self, seq):
        if isinstance(seq, Term):
            seq = (seq,)
        rule = Rule(self.to_cpd(), tuple(map(Term.to_cpd, seq)))
        kbmeta.kb._add_rule(rule)

    def to_cpd(self):
        return Cpd(self.name, tuple(self.args))


class Reader(object):
    def __setitem__(self, k, v): pass
    def __getitem__(self, k): return Term(k)


class kbmeta(type):
    kb = None
    @classmethod
    def __prepare__(cls, n, b, **kw):
        kbmeta.kb = KB()
        return Reader()
    def __new__(cls, n, b, kw):
        return kbmeta.kb

