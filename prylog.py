# Subgrammar for FOL-Sentence
#
# Sen      : SenAtom | SenCplx
# SenAtom  : Pred    | Pred Term* | Term == Term | Term != Term | Assert Term
# SenCplx  : AND Sen Sen
#          | Or  Sen Sen
#          | IMP Sen Sen
#          | EQV Sen Sen
#          | Qua Var* Sen
# Qua      : FORALL | EXISTS
# Pred     : TRUE | FALSE | UserPred
# UserPred : IDENTIFIER

# Subgrammar for Term
# 
# Term     : TermFunc | TermCnpd | Const | Var | ScmVar
# TermFunc : FUNC FUNCOP Term*
# TermCnpd : DATA CONSTR Term* | List
# List     : NIL | CONS Term List 
# Const    : NUMBER | STRING | BOOLEAN
# Var      : VARSYMBOL
# ScmVar   : SCMSYMBOL

# === FOL-Structures ===

class Sen(object):
    def __init__(self, *subs):
        self.subs = subs
    def __and__(self, other):
        return And(self, other)
    def __or__(self, other):
        return Or(self, other)
    def __not__(self):
        return Not(self)
    def __le__(self, other):
        return Rule(self, other)
    def __repr__(self):
        return '{}{}'.format(self.__class__.__name__, self.subs)

class And(Sen):
    def __repr__(self):
        return '{} & {}'.format(*self.subs)
class Or(Sen): pass
class Not(Sen): pass
class Rule(Sen):
    def __repr__(self):
        return '{{{} <= {}}}'.format(self.lhs, self.rhs)
    @property
    def lhs(self): return self.subs[0]
    @property
    def rhs(self): return self.subs[1]
    @property
    def key(self):
        return self.lhs.verb

class SenAtom(Sen): pass
class Pred(SenAtom):
    """A predicate is upon 0 or more terms.

    A term can be a constant, Variable or Schematic Variable when
    defining rule.

    """
    def __init__(self, verb, *terms):
        assert type(verb) is str
        self.verb = verb
        self.terms = terms
    def __repr__(self):
        return '{}/{}{}'.format(self.verb, self.arity, list(self.terms) or '')
    def __call__(self, *terms):
        self.terms = terms
        return self
    @property
    def arity(self):
        return len(self.terms)
    @property
    def key(self):
        return self.verb

class Eq(SenAtom):
    "Eq is a special Atomic Sentence on 2 terms."
    def __repr__(self):
        t1, t2 = self.subs
        return '({} == {})'.format(t1, t2)
class NotEq(SenAtom):
    "NotEq is a special Atomic Sentence on 2 terms."
    def __repr__(self):
        t1, t2 = self.subs
        return '({} != {})'.format(t1, t2)


class Term(object):
    "Abstract class."
    def __init__(self, *a, **kw):
        raise NotImplementedError('Need override constructor in derived subclasses.')

class Var(Term):
    def __init__(self, symbol):
        self.symbol = symbol
    def __repr__(self):
        return '${}'.format(self.symbol)
    def __hash__(self):
        return hash(self.symbol)
    def __eq__(self, other):
        return type(other) == type(self) and self.symbol == other.symbol

class ScmVar(Term):
    """Schematic/Template Variable is a special term only used during
    defining rules.

    One such variable is instantiated to Variable by Universal
    Instantiation (standardize-apart) during ask/query.

    """
    def __init__(self, mark):
        self.mark = mark
    def __repr__(self):
        return '?{}'.format(self.mark)
    def __eq__(self, other):
        return type(self) == type(other) and self.mark == other.mark
    def __hash__(self):
        return hash(self.mark)

class Func(Term):
    "Func is a lazy object for function application."
    def __init__(self, op, *args):
        self.op = op
        self.args = args
    def __iter__(self):
        yield self.op
        yield self.args
    def __repr__(self):
        # op_name = self.op.__name__
        # return '{}{}'.format(op_name, self.args or '')
        return '{}{}'.format(self.op, self.args or '')
    def __hash__(self):
        return hash(self.op)
    def eval(self):
        return self.op(*self.args)
    def can_eval(self):
        return all(type(a) not in (Var, Func) for a in self.args)


def Assert(func):
    return Eq(True, func)

# === Easy Use ===
def easy(cls):
    class _E(object):
        def __getattr__(self, k):
            return cls(k)
    cls.new = _E()
    # return cls
    return cls.new
            
var = easy(Var)
scm = easy(ScmVar)
pred = easy(Pred)


# === Unification | Substitution | Evaluation ===

FAIL = '-FAIL-'

def unify(x, y, u={}):
    "Unification can apply to `Term` as well as `Pred`."
    if u is FAIL:
        return FAIL

    # unify Term (9-cases in total)
    # - Constant Term: c=c
    elif x == y:
        return u
    # - Variable Term: v=v, v=c|v=f, c=f|v=f
    elif type(x) == Var:
        return unify_var(x, y, u)
    elif type(y) == Var:
        return unify_var(y, x, u)
    # - Functional Term: f=f, f=c|c=f
    # 
    # FIXME: To suppress the need with cases involving Func, keep
    # every targeted Func instance evaluated before entering `unify`.
    elif type(x) == Func or type(y) == Func:
        raise ValueError('Unsupport unification for unevaluated Func.')

    # unify Atomic Sentence
    # - Eq/NotEq
    #   Verify both to be true?
    # - User Predicate
    elif type(x) == type(y) == Pred:
        if x.verb != y.verb:
            return FAIL
        # Allow variable to bind to any predicate verb, i.e. allow
        # variable to represent Relations (predicate symbols, verbs)
        # besides Constants (subjective/objective)?
        # u = unify(x.verb, y.verb, u)
        for a, b in zip(x.terms, y.terms):
            u = unify(a, b, u)
            if u is FAIL: break
        return u

    # unify Complex Sentence
    elif isinstance(x, Sen) and isinstance(y, Sen):
        if type(x) == type(y):
            for a, b in zip(x.subs, y.subs):
                u = unify(a, b, u)
                if u is FAIL: break
        return FAIL

    # type inconsistent
    else:
        return FAIL

def unify_var(v, z, u):
    "Try append a consistent binding `v: z` into unifier `u`."
    assert type(v) == Var
    if u is FAIL:
        return FAIL
    elif v in u:
        return unify(u[v], z, u)
    elif z in u:
        return unify(v, u[z], u)
    else:
        u1 = dict(u); u1[v] = z
        return u1

def vars_from(x, m=None):
    if m is None: m = set()
    if isinstance(x, Var):
        if x not in m:
            m.add(x)
            yield x
    elif isinstance(x, Func):
        for arg in x.args:
            yield from vars_from(arg, m)
    elif isinstance(x, Pred):
        for term in x.terms:
            yield from vars_from(term, m)
    elif isinstance(x, Sen):
        for sub in x.subs:
            yield from vars_from(sub, m)
        

def subst(u, x):
    """Substitute `u[x]` for `x` recursively.

    - Evaluate `Func` when possible, since this comprises also some
    kind of 'substitute'

    """
    if isinstance(x, Var):
        if x in u: return u[x]
        else:      return x
    elif isinstance(x, Pred):
        return Pred(x.verb, *(subst(u, y) for y in x.terms))
    elif isinstance(x, Sen):
        return type(x)(*[subst(u, y) for y in x.subs])
    elif isinstance(x, Func):
        # Eval func here?
        # Post-order here!
        f = Func(x.op, *(subst(u, a) for a in x.args))
        if f.can_eval(): return f.eval()
        else:            return f
    else:
        # Constant
        return x

from itertools import count
stand_count = count()
def univ_inst(x, u=None):
    "Instantiate ScmVar to Var."
    # assert isinstance(x, (ScmVar, Sen)), type(x)
    if u is None: u = {}
    if isinstance(x, ScmVar):
        if x not in u:
            u[x] = Var('{}_{}'.format(x.mark, next(stand_count)))
        return u[x]
    elif isinstance(x, Var):
        raise
    elif isinstance(x, Func):
        return Func(x.op, *(univ_inst(a, u) for a in x.args))
    elif isinstance(x, Pred):
        return Pred(x.verb, *(univ_inst(y, u) for y in x.terms))
    elif isinstance(x, Sen):
        return type(x)(*(univ_inst(y, u) for y in x.subs))
    else:
        # Constant
        return x

def stand_reset():
    global stand_count
    stand_count = count()


# === Knowledge Base ===
# 
# Properties of a KB
# + tell: register a logical sentence
# + ask : perform a query
# + indexing: quick retrieval of matching sentences w.R.t.
#   - verifying a new tell
#   - a real-time query

class KB(object):
    def __init__(self):
        self.facts = {}
        self.rules = {}
    def __repr__(self):
        from pprint import pformat
        return pformat((self.facts, self.rules))

    # Augmenting KB
    def tell(self, sen):
        """Let the KB tell a sentence, which can be either
        - An Atomic Sentence or
        - A Definite Clause (Rule).
        Complex Sentence supported?
        """
        if isinstance(sen, SenAtom):
            if isinstance(sen, Pred):
                self.add_fact(sen)
            elif isinstance(sen, Eq): pass
            elif isinstance(sen, NotEq): pass
            else: raise
        elif isinstance(sen, Rule):
            self.add_rule(sen)
        elif isinstance(sen, (And, Or, Not)):
            raise NotImplemented

    def has_fact(self, pred):
        return pred.verb in self.facts
    def add_fact(self, pred):
        if pred.key not in self.facts:
            self.facts[pred.key] = []
        self.facts[pred.key].append(pred)
    def get_facts(self, symbol):
        if symbol in self.facts:
            yield from self.facts[symbol]

    def has_rule(self, pred):
        return pred.key in self.rules
    def add_rule(self, rule):
        if rule.key not in self.rules:
            self.rules[rule.key] = []
        self.rules[rule.key].append(rule)
    def get_rules(self, key):
        if key in self.rules:
            yield from self.rules[key]

    # ASK
    def ask(kb, goal):
        stand_reset()
        vs = set(vars_from(goal))
        for u in kb.ask_1(goal, {}):
            yield {v: u[v] for v in vs}

    # Dispatch ASK
    def ask_1(kb, goal0, u):
        goal = subst(u, goal0)
        # !query Atomic Sentence
        if isinstance(goal, SenAtom):
            yield from kb.ask_atom(goal, u)
        # !query Complex Sentence
        elif isinstance(goal, Not):
            yield from kb.ask_not(goal, u)
        elif isinstance(goal, And):
            yield from kb.ask_and(goal, u)
        elif isinstance(goal, Or):
            yield from kb.ask_or(goal, u)
        elif isinstance(goal, Rule):
            yield from kb.ask_rule(goal, u)
        else:
            raise ValueError('Illegal goal: {}'.format(goal0))
    
    # ASK for Atomic Sentence
    def ask_atom(kb, goal, u):
        'Dispatch Atomic Sentence asked.'
        if isinstance(goal, Eq):
            yield from kb.ask_eq(goal, u)
        elif isinstance(goal, NotEq):
            yield from kb.ask_not_eq(goal, u)
        else:
            yield from kb.ask_pred(goal, u)

    def ask_eq(kb, goal, u):
        s1, s2 = goal.subs
        u1 = unify(s1, s2, u)
        if u1 is not FAIL:
            yield u1

    def ask_not_eq(kb, goal, u):
        s1, s2 = goal.subs
        u1 = unify(s1, s2, u)
        if u1 is FAIL:
            yield u

    def ask_pred(kb, goal, u):
        yield from kb.ask_fact(goal, u)
        yield from kb.ask_rule(goal, u)

    # ASK for Complex Sentence 
    def ask_or(kb, goal, u):
        for sub in goal.subs:
            yield from kb.ask_1(sub, u)

    def ask_and(kb, a, u):
        if type(a) is And:
            l, r = a.subs
            for u1 in kb.ask_and(l, u):
                for u2 in kb.ask_1(r, u1):
                    yield u2
        else:
            yield from kb.ask_1(a, u)

    def ask_not(kb, goal, u):
        if not any(kb.ask_1(goal, u)):
            yield u

    # Ask for simple goal.
    def ask_fact(kb, goal, u):
        for fact in kb.get_facts(goal.key):
            u1 = unify(fact, goal, u)
            if u1 is not FAIL:
                yield u1

    def ask_rule(kb, goal, u):
        for rule in kb.get_rules(goal.key):
            rule1 = univ_inst(rule)
            u1 = unify(rule1.lhs, goal, u)
            if u1 is not FAIL:
                yield from kb.ask_and(rule1.rhs, u1)
            # Retract standardized-apart-counter?
            pass


# Test

kb = KB()

# Pred(str:<verb>, str:<Const>, str:<Const>)
# kb.tell(pred.father('pap', 'a'))
# kb.tell(father=[])

kb.tell(Pred('father', 'pap', 'a'))
kb.tell(Pred('father', 'pap', 'b'))
kb.tell(Pred('mother', 'mum', 'a'))
kb.tell(Pred.new.mother('mum', 'b'))
kb.tell(pred.father('opa', 'pap'))
kb.tell(pred.mother('oma', 'pap'))
kb.tell(Pred('sibling', ScmVar('x'), ScmVar('y'))
        <=
        Pred('father', ScmVar('z'), ScmVar('x')) &
        Pred('father', ScmVar('z'), ScmVar('y')) &
        NotEq(ScmVar('x'), ScmVar('y'))
)

kb.tell(
    pred.ancester(scm.x, scm.y)
    <=
    pred.father(scm.x, scm.y)
)
# kb.tell(
#     Pred('ancester', ScmVar('x'), ScmVar('y'))
#     <=
#     Pred('father', ScmVar('x'), ScmVar('y'))
# )
kb.tell(
    Pred('ancester', scm.x, scm.y)
    <=
    Pred('father', scm.x, scm.z) &
    Pred('ancester', scm.z, scm.y)
)

from pprint import pprint
pprint(kb)

q = kb.ask(Pred('father', Var('x'), Var('y')))
pprint(list(q))

print('========== sibling ==========')
q = kb.ask(Pred('sibling', Var('x'), Var('y')))
pprint(list(q))

q = kb.ask(Pred('sibling', Var('x'), Var('y')))
pprint(list(q))

print('========== ancester ==========')
q = kb.ask(Pred('ancester', var.U, var.V))
pprint(list(q))

print('========== factorial ==========')
# q = kb.ask(Pred('factorial', 0, var.W))
import operator as op

kb.tell(
    Pred('factorial', 0, 1)
)
kb.tell(
    Pred('factorial', scm.x, scm.y)
    <=
    Assert(Func(op.gt, scm.x, -1)) &
    Pred('factorial', Func(op.sub, scm.x, 1), scm.y1) &
    Eq(scm.y, Func(op.mul, scm.x, scm.y1))
)
# Dead loop when asking for more than one answer...
# Since it is not ruled out that (scm.x > -1)
# Eq(True, Func(...)) can do the trick

q = kb.ask(Pred('factorial', 2, var.W))
pprint(list(q))
q = kb.ask(Pred('factorial', 5, var.W))
pprint(list(q))


print('========== more tinies ==========')
kb.tell(pred.gt5(scm.x) <= Assert(Func(op.gt, scm.x, 5)))
q = kb.ask(pred.gt5(8))
pprint(list(q))
q = kb.ask(pred.gt5(4))
pprint(list(q))
