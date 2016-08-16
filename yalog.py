from collections import namedtuple
from collections import defaultdict as ddict

## =========================
##      Data Structure
## =========================

Var = namedtuple('Var', 'name')
Var.__repr__ = lambda s: s.name

Cpd = namedtuple('Cpd', 'op args')
Cpd.__repr__ = lambda s: (s.op) + repr(s.args)


class KB(object):

    class Query(object):
        def __init__(self, kb, op):
            self.kb = kb
            self.op = op
        def __getitem__(self, args):
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
    def _add_fact(self, name, fact):
        self._facts[name].append(fact)
    def _add_rule(self, op, rule):
        self._rules[op].append(rule)

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

def subst(u, e, ctr=None):
    if type(e) == Var:
        if e in u: return u[e]
        else: return e
    elif type(e) == Cpd:
        return Cpd(e.op, tuple(subst(u, a, ctr) for a in e.args))
    elif type(e) in (tuple, list):
        return tuple(subst(u, x) for x in e)
    else:
        return e


from itertools import count

std_ctr = count()
def stand_vars(rule):
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
    for u in bc_or(kb, query, {}):
        # Hide intermediate variables
        yield {k: u[k] for k in u if k in qvs}

def bc_or(kb, goal, u):
    if kb._has_fact(goal):
        for fact in kb[goal.op]:
            u1 = unify(fact, goal, u)
            if not fails(u1):
                yield u1
    elif kb._has_rule(goal):
        for csqt, prms in kb[goal.op]:
            if not fails(unify(csqt, goal)):
                csqt, prms = stand_vars((csqt, prms))
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
        for u1 in bc_or(kb, subst(u, goals[0]), u):
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


class kbmeta(type):

    kb = None

    class Term(object):

        def __init__(self, name):
            self.name = name
            self.followers = [self]

        def __setitem__(self, args, v):
            if not type(v) in (tuple, list):
                v = (v,)
            op = self.name
            c = Cpd(op, args), v
            kbmeta.kb._add_rule(op, c)

        def __getitem__(self, args):
            c = Cpd(self.name, args)
            self.term = c
            if any(isinstance(a, Var) for a in args):
                return c
            else:
                kbmeta.kb._add_fact(self.name, c)
                return c

        # operators
        # def __call__(self, *args):
        #     return self.__getitem__(args)
        # def __and__(self, other):
        #     self.followers.append(other)
        #     return self
        # def __le__(self, ts):
        #     rule = (self.term, tuple(t.term for t in ts))
        #     op = self.name
        #     kbmeta.kb._add_rule(op, rule)

    class Reader(object):

        def __setitem__(self, k, v):
            kbmeta.kb._add_attr(k, v)

        def __getitem__(self, k):
            if str.isupper(k):
                return Var(k)
            else:
                return kbmeta.Term(k)

    @classmethod
    def __prepare__(mcls, n, b, **kw):
        kbmeta.kb = KB()
        return kbmeta.Reader()

    def __new__(mcls, n, b, reader):
        kb = kbmeta.kb
        kbmeta.kb = None
        return kb
