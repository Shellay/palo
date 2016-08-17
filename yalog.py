from collections import namedtuple, deque
from collections import defaultdict as ddict

## =========================
##      Data Structure
## =========================

Var = namedtuple('Var', 'name')
Var.__repr__ = lambda s: s.name

Cpd = namedtuple('Cpd', 'op args')
Cpd.__repr__ = lambda s: '{}{}'.format(s.op, tuple(s.args))

# Rule = namedtuple('Rule', 'csqt prms')
# Rule.__repr__ = lambda s: '{{{} <= {}}}'.format(*s)


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

_NOT = 'not'
_EQ = 'eq'
_NE = 'not_eq'

def bc_or(kb, goal, u):
    # How about when goal is eq(A, B), not_eq(A, B) and similar?
    # - demodulation/paramodulation
    # - equational unification
    if goal.op == _EQ:
        u1 = unify(*goal.args, u)
        if not fails(u1):
            yield u1
    elif goal.op == _NE:
        u1 = unify(*goal.args, u)
        if fails(u1):
            yield u
    elif kb._has_fact(goal):
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


class Expr(object):
    def __init__(self, op1, op2):
        self.op1 = op1; self.op2 = op2
    def __and__(self, other):
        return And(self, other)
    def __or__(self, other):
        return Or(self, other)
class And(Expr): pass
class Or(Expr): pass


class Term(Expr):

    def __init__(self, name):
        self.name = name

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

    def __le__(self, other):
        disj = deque()
        while 1:
            if type(other) is Or:
                disj.appendleft(other.op2)
                other = other.op1
            else:
                disj.appendleft(other)
                break
        for conj in disj:
            seq = deque()
            while 1:
                if type(conj) is And:
                    seq.appendleft(conj.op2)
                    conj = conj.op1
                else:
                    seq.appendleft(conj)
                    break
            rule = (self.to_cpd(), tuple(map(Term.to_cpd, seq)))
            kbmeta.kb._add_rule(rule)

    def __eq__(self, other):
        return Term(_EQ)(self, other)

    def __ne__(self, other):
        return Term(_NE)(self, other)

    def to_cpd(self): return Cpd(self.name, tuple(self.args))


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

