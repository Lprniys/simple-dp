from itertools import chain, product
import copy
import time

pool = {}
proof = {}

def comb(iterable, r):
    # combinations('ABCD', 2) --> AB AC AD BC BD CD
    # combinations(range(4), 3) --> 012 013 023 123
    pool = list(iterable)
    n = len(pool)
    if r > n:
        return
    indices = list(range(r))
    yield list(pool[i] for i in indices)
    while True:
        for i in reversed(range(r)):
            if indices[i] != i + n - r:
                break
        else:
            return
        indices[i] += 1
        for j in range(i+1, r):
            indices[j] = indices[j-1] + 1
        yield list(pool[i] for i in indices)

# def product(*args, **kwds):
#     # product('ABCD', 'xy') --> Ax Ay Bx By Cx Cy Dx Dy
#     # product(range(2), repeat=3) --> 000 001 010 011 100 101 110 111
#     pools = map(tuple, args) * kwds.get('repeat', 1)
#     result = [[]]
#     for pool in pools:
#         result = [x+[y] for x in result for y in pool]
#     for prod in result:
#         yield tuple(prod)

def genPool(S):
    l = chain.from_iterable(comb(S,n) for n in range(len(S)+1))
    s = product(l, repeat = 2)
    system = []
    for i in s:
        system.append(Sequent(i[0],i[1]))
    return system

class Sequent:
    def __init__(self, ante, succ):
        self.ante = ante
        self.succ = succ
        self.cache = []
        for wff1 in ante:  #waiting for another solution
            self.cache.append(wff1)
        for wff2 in succ:
            self.cache.append(wff2)
        self.wffs = [wff for wff in self.cache]
        if any(not (isinstance(c, Formula)) for c in self.wffs):
            return 'Badly formed Sequent'

    def __str__(self):
        return "Sequent({0!s}, {1!s})".format(self.ante, self.succ)

    def __repr__(self):
        return str(self)

    def __eq__(self, other):
        if not isinstance(other, Sequent):
            return False
        for wff in self.ante:
            if wff not in other.ante:
                return False
        for wff in self.succ:
            if wff not in other.succ:
                return False
        for wff in other.ante:
            if wff not in self.ante:
                return False
        for wff in other.succ:
            if wff not in self.succ:
                return False
        return True

    def __hash__(self):
        return hash(str(self))

    def extractSubs(self):
        subs = []
        clean = []
        for wff in self.wffs:
            s = wff.extractSubs()
            subs.extend(s)
        for sub in subs:
            flag = False
            for c in clean:
                if c == sub:
                    flag = True
                    break
            if not flag:
                clean.append(sub)
        return clean
        
class Formula:
    def __init__(self):
        pass

class Atom(Formula):
    def __init__(self, literal):
        self.literal = literal
        self.key = 'Atom'
        Formula.__init__(self)

    def __str__(self):
        return "{0!s}".format(self.literal)

    def __repr__(self):
        return str(self)

    def __eq__(self, other):
        if not isinstance(other, Atom):
            return False
        return self.literal == other.literal

    def __hash__(self):
        return hash(str(self))

    def extractSubs(self):
        return [self]

class And(Formula):
    """
    Represents a conjunction of formulas.
    """

    def __init__(self, *conjuncts1):
        """
        conjuncts is a list of Formulas
        """
        if any(isinstance(c, bool) and not c for c in conjuncts1):
            self.conjuncts = []
            Formula.__init__(self)
            return
        conjuncts = [c for c in conjuncts1 if not isinstance(c, bool)]
        if any(not (isinstance(c, Formula)) for c in conjuncts):
            return 'Badly formed And'
        self.conjuncts = conjuncts
        self.key = 'And'
        Formula.__init__(self)

    def __str__(self):
        return "And({0!s})".format(', '.join(str(s) for s in self.conjuncts))

    def __repr__(self):
        return str(self)

    def __eq__(self, other):
        if not isinstance(other, And):
            return False
        if len(self.conjuncts) != len(other.conjuncts):
            return False
        else:
            for i in range(len(self.conjuncts)):
                if not self.conjuncts[i] == other.conjuncts[i]:
                    return False
            return True

    def __hash__(self):
        return hash(str(self))

    def substitute(self, map):
        return And(*[c.substitute(map) for c in self.conjuncts])

    def extractSubs(self):
        subs = [self]
        for wff in self.conjuncts:
            s = wff.extractSubs()
            subs.extend(s)
        return subs

class Or(Formula):
    """
    Represents a disjunction of formulas.
    """

    def __init__(self, *disjuncts1):
        """
        disjuncts is a list of Formulas
        """
        if any(isinstance(c, bool) and c for c in disjuncts1):
            self.disjuncts = [terms.one == terms.one]
            Formula.__init__(self)
            return
        disjuncts = [d for d in disjuncts1 if not isinstance(d, bool)]

        if any(not (isinstance(c, Formula)) for c in disjuncts):
            print(disjuncts)
            return 'Badly formed Or'
        self.disjuncts = disjuncts
        self.key = 'Or'
        Formula.__init__(self)

    def __str__(self):
        return "Or({0!s})".format(', '.join(str(s) for s in self.disjuncts))

    def __repr__(self):
        return str(self)

    def __eq__(self, other):
        if not isinstance(other, Or):
            return False
        if len(self.disjuncts) != len(other.disjuncts):
            return False
        else:
            for i in range(len(self.disjuncts)):
                if not self.disjuncts[i] == other.disjuncts[i]:
                    return False
            return True

    def __hash__(self):
        return hash(str(self))
        
    def substitute(self, map):
        return Or(*[d.substitute(map) for d in self.disjuncts])

    def extractSubs(self):
        subs = [self]
        for wff in self.disjuncts:
            s = wff.extractSubs()
            subs.extend(s)
        return subs


class Not(Formula):
    """
    Represents the negation of a formula
    """

    def __init__(self, formula):
        if not isinstance(formula, Formula):
            print("BAD:", formula)
            return 'Badly formed Not:' + str(formula)
        self.formula = formula
        self.key = 'Not'
        Formula.__init__(self)

    def negate(self):
        """
        Pushes the negation through self.formula to remove the not.
        """
        # if isinstance(self.formula, terms.TermComparison):
        #     return terms.TermComparison(self.formula.term1,
        #                                 terms.comp_negate(self.formula.comp),
        #                                 self.formula.term2)

        if isinstance(self.formula, And):
            return Or(*[Not(a) for a in self.formula.conjuncts])

        elif isinstance(self.formula, Or):
            return And(*[Not(a) for a in self.formula.disjuncts])

        elif isinstance(self.formula, Not):
            return self.formula.formula

        elif isinstance(self.formula, Implies):
            return And(self.formula.hyp, Not(self.formula.con))

        elif isinstance(self.formula, Univ):
            return Exist(self.formula.vars, Not(self.formula.formula))

        elif isinstance(self.formula, Exist):
            return Univ(self.formula.vars, Not(self.formula.formula))

    def __str__(self):
        return "Not({0!s})".format(self.formula)

    def __repr__(self):
        return str(self)

    def __eq__(self, other):
        if not isinstance(other, Not):
            return False
        return self.formula == other.formula

    def __hash__(self):
        return hash(str(self))
        
    def substitute(self, map):
        return Not(self.formula.substitute(map))

    def extractSubs(self):
        return [self,self.formula]


class Implies(Formula):
    """
    Represents the formula a->b
    """

    def __init__(self, hyp, con):
        if any(not isinstance(c, Formula) for c in [hyp, con]):
            return 'Badly formed Implies'
        self.hyp, self.con = hyp, con
        self.key = 'Implies'
        Formula.__init__(self)

    def __str__(self):
        return "Implies({0!s}, {1!s})".format(self.hyp, self.con)

    def __repr__(self):
        return str(self)

    def __eq__(self, other):
        if not isinstance(other, Implies):
            return False
        return self.hyp == other.hyp and self.con == other.con

    def __hash__(self):
        return hash(str(self))
        
    def substitute(self, map):
        return Implies(self.hyp.substitute(map), self.con.substitute(map))

    def extractSubs(self):
        subs = [self]
        for wff in [self.hyp,self.con]:
            s = wff.extractSubs()
            subs.extend(s)
        return subs

def genInits(subs):
    inits = []
    for sub in subs:
        if isinstance(sub, Atom):
            inits.append(Sequent([sub],[sub]))
    return inits

def haveCommon(list1, list2):
    for e in list1:
        if e in list2:
            return True,e
    return False, None

def haveOneDifference(list1, list2): #duplicate sensible
    gap = len(list1) - len(list2)
    if gap != 0:
        return False, gap
    counter = 0
    for e in list1:
        if e not in list2:
            counter += 1
            formula1 = e
    if counter != 1:
        return False, None
    counter = 0
    for k in list2:
        if k not in list1:
            counter += 1
            formula2 = k
    if counter != 1:
        return False, None
    return True, formula1, formula2

def weakening_left(upper, lower):
    if set(upper.succ) == set(lower.succ) and \
    len(set(upper.ante)) + 1 == len(set(lower.ante)) and \
    set(upper.ante) <= set(lower.ante):
        return True
    return False

def weakening_right(upper, lower):
    if set(upper.ante) == set(lower.ante) and \
    len(set(upper.succ)) + 1 == len(set(lower.succ)) and \
    set(upper.succ) <= set(lower.succ):
        return True
    return False

# def contraction_left(upper, lower):
#     if set(upper.ante) == set(lower.ante) and \
#     len(set(upper.succ)) + 1 == len(set(lower.succ)) and \
#     set(upper.succ) <= set(lower.succ):
#         return True
#     return False

def cut(upper1, upper2, lower):
    cutInfo = haveCommon(upper1.succ, upper2.ante)
    if not cutInfo[0]:
        return False
    if not set(upper1.ante) <= set(lower.ante):
        return False
    if not set(upper2.succ) <= set(lower.succ):
        return False
    #print '{0!s},{1!s},{2!s}'.format(upper1,upper2,lower)
    u1 = copy.deepcopy(upper1)
    u2 = copy.deepcopy(upper2)
    u1.succ.remove(cutInfo[1])
    u2.ante.remove(cutInfo[1])
    if set(u1.succ) <= set(lower.succ) and \
    set(u2.ante) <= set(lower.ante):
        return True
    return False

def not_left(upper, lower):
    if len(upper.succ) - len(lower.succ) != 1:
        return False
    if len(lower.ante) - len(upper.ante) != 1:
        return False
    if not set(lower.succ) <= set(upper.succ):
        return False
    if not set(upper.ante) <= set(lower.ante):
        return False
    auxiliary = list(set(upper.succ) - set(lower.succ))[0]
    principal = list(set(lower.ante) - set(upper.ante))[0]
    if principal == Not(auxiliary):
        return True
    return False

def not_right(upper, lower):
    if len(lower.succ) - len(upper.succ) != 1:
        return False
    if len(upper.ante) - len(lower.ante) != 1:
        return False
    if not set(upper.succ) <= set(lower.succ):
        return False
    if not set(lower.ante) <= set(upper.ante):
        return False
    auxiliary = list(set(upper.ante) - set(lower.ante))[0]
    principal = list(set(lower.succ) - set(upper.succ))[0]
    if principal == Not(auxiliary):
        return True
    return False

def and_left(upper, lower):
    if set(upper.succ) != set(lower.succ):
        return False
    andInfo = haveOneDifference(upper.ante, lower.ante)
    if not andInfo[0]:
        if andInfo[1] != 1:
            return False
        if not set(lower.ante) < set(upper.ante):
            return False
        potential_aux = set(upper.ante) - set(lower.ante)
        auxiliary = list(potential_aux)[0]
        for wff in lower.ante:
            if isinstance(wff, And):
                if auxiliary in wff.conjuncts:
                    return True
        return False
    else:
        auxiliary = andInfo[1]
        principal = andInfo[2]
        if not isinstance(principal, And):
            return False
        if auxiliary in principal.conjuncts:
            return True
        return False

def and_right(upper1, upper2, lower):  #conjuncts formation sensible
    if set(upper1.ante) != set(upper2.ante) or \
    set(upper1.ante) != set(lower.ante):
        return False
    upperInfo = haveOneDifference(upper1.succ, upper2.succ)
    andInfo = haveOneDifference(upper1.succ, lower.succ)
    if not upperInfo[0]:
        return False
    if not andInfo[0]:
        if andInfo[1] != 1:
            return False
        if not set(lower.succ) < set(upper1.succ) or \
        not set(lower.succ) < set(upper2.succ):
            return False
        potential_aux1 = set(upper1.succ) - set(lower.succ)
        potential_aux2 = set(upper2.succ) - set(lower.succ)
        auxiliary1 = list(potential_aux1)[0]
        auxiliary2 = list(potential_aux2)[0]
        for wff in lower.succ:
            if isinstance(wff, And):
                if auxiliary1 in wff.conjuncts and auxiliary2 in wff.conjuncts:
                    return True
        return False
    else:
        principal = andInfo[2]
        if not isinstance(principal, And):
            return False
        if upperInfo[1] in principal.conjuncts and upperInfo[2] in principal.conjuncts:
            return True
        return False

def or_left(upper1, upper2, lower):  #disjuncts formation sensible
    if set(upper1.succ) != set(upper2.succ) or \
    set(upper1.succ) != set(lower.succ):
        return False
    upperInfo = haveOneDifference(upper1.ante, upper2.ante)
    orInfo = haveOneDifference(upper1.ante, lower.ante)
    if not upperInfo[0]:
        return False
    if not orInfo[0]:
        if orInfo[1] != 1:
            return False
        if not set(lower.ante) < set(upper1.ante) or \
        not set(lower.ante) < set(upper2.ante):
            return False
        potential_aux1 = set(upper1.ante) - set(lower.ante)
        potential_aux2 = set(upper2.ante) - set(lower.ante)
        auxiliary1 = list(potential_aux1)[0]
        auxiliary2 = list(potential_aux2)[0]
        for wff in lower.ante:
            if isinstance(wff, Or):
                if auxiliary1 in wff.disjuncts and auxiliary2 in wff.disjuncts:
                    return True
        return False
    else: 
        principal = orInfo[2]
        if not isinstance(principal, Or):
            return False
        if upperInfo[1] in principal.disjuncts and upperInfo[2] in principal.disjuncts:
            return True
        return False

def or_right(upper, lower):
    if set(upper.ante) != set(lower.ante):
        return False
    orInfo = haveOneDifference(upper.succ, lower.succ)
    if not orInfo[0]:
        if orInfo[1] != 1:
            return False
        if not set(lower.succ) < set(upper.succ):
            return False
        potential_aux = set(upper.succ) - set(lower.succ)
        auxiliary = list(potential_aux)[0]
        for wff in lower.succ:
            if isinstance(wff, Or):
                if auxiliary in wff.disjuncts:
                    return True
        return False
    else:
        auxiliary = orInfo[1]
        principal = orInfo[2]
        if not isinstance(principal, Or):
            return False
        if auxiliary in principal.disjuncts:
            return True
        return False

# def Implies_left(upper1, upper2, lower):
#     pass

def isInit(seq):
    if set(seq.ante) == set(seq.succ):
        return True
    return False

def genProof(goal, pool):
    global proof
    if not isInit(goal):
        proof[goal] = pool[goal]
        for g in proof[goal][0]:
            genProof(g, pool)


def findProof(proven, potential, goal):
    global pool
    S = []
    for lower in potential:
        for upper in proven:
            if weakening_left(upper, lower):
                S.append(lower)
                pool[lower] = [upper], 'weakening_left'
                # print 'trying weakening_left on ({0!s}, {1!s})'.format(str(upper),str(lower))
                break
            if weakening_right(upper, lower):
                S.append(lower)
                pool[lower] = [upper], 'weakening_right'
                # print 'trying weakening_right on ({0!s}, {1!s})'.format(str(upper),str(lower))
                break
            if not_left(upper, lower):
                S.append(lower)
                pool[lower] = [upper], 'not_left'
                break
            if not_right(upper, lower):
                S.append(lower)
                pool[lower] = [upper], 'not_right'
                break
            if and_left(upper, lower):
                S.append(lower)
                pool[lower] = [upper], 'and_left'
                break
            if or_right(upper, lower):
                S.append(lower)
                pool[lower] = [upper], 'or_right'
                break
        if lower in S:
            continue
        for uppers in list(comb(proven, 2)):
            # if cut(uppers[0], uppers[1], lower) or \
            # cut(uppers[1], uppers[0], lower):
            #     S.append(lower)
            #     pool[tuple(uppers)] = lower, 'cut'
            #     # print 'trying cut on ({0!s}, {1!s})'.format(str(uppers[0]),str(uppers[1]),str(lower))
            #     break
            if and_right(uppers[0], uppers[1], lower) or \
            and_right(uppers[1], uppers[0], lower):
                S.append(lower)
                pool[lower] = tuple(uppers), 'and_right'
                break
            if or_left(uppers[0], uppers[1], lower) or \
            or_left(uppers[1], uppers[0], lower):
                S.append(lower)
                pool[lower] = tuple(uppers), 'or_left'
                break
    if not S:
        # print 'unprovable, depth: {0!s}'.format(str(depth))
        print('result : unprovable')
        print('Proof:')
        return
    if goal in S:
        print('result : provable')
        # print(pool)
        genProof(goal, pool)
        print('Proof:')
        return proof
    potential = set(potential) - set(S)
    proven = set(proven) | set(S)
    return findProof(proven, potential, goal)

def check(sequent):
    print('checking provability: {0!s}'.format(sequent))
    S1 = list(genPool(sequent.extractSubs()))
    S0 = genInits(sequent.extractSubs())
    potential = set(S1) - set(S0)
    proven = set(genInits(sequent.extractSubs()))
    return findProof(proven, potential, sequent)

# test = Implies(Or((Atom('A')),Atom('B')),And(Atom('B'),Atom('C')))

# testt = Implies(Or((Atom('A')),Atom('C')),And(Atom('B'),Atom('C')))

# tests = Sequent([test],[])

# test1 = Sequent([Atom('A')],[test,Atom('A')])

# print test1.extractSubs()

ttest = Sequent([And(Atom('A'),Atom('B'))],[And(Atom('A'),Atom('B'))])

t0 = Sequent([],[And(Atom('A'),Not(Atom('A')))])

t1 = Sequent([Atom('A')],[Not(Atom('A'))])

t2 = Sequent([And(Atom('A'),Not(Atom('A')))],[])

t3 = Sequent([],[Or(Atom('A'),Not(Atom('A')))])

t4 = Sequent([],[Not(Atom('A')), Or(Not(Atom('B')), Atom('A'))])

t5 = Sequent([],[Not(Atom('A')),Not(Not(Atom('A')))])

time_start = time.time()
print(check(t4))
time_end = time.time()
print('time cost: {0}'.format(time_end - time_start))

# print(genPool(Sequent([Atom('A')],[Atom('B'), Atom('C')]).extractSubs()))