#!/usr/bin/env python3
"""Deterministic finite D1 tests. These are C evidence, never Lean/kernel evidence."""
from __future__ import annotations
from dataclasses import dataclass
from itertools import permutations, product
from functools import lru_cache
import hashlib, json, pathlib, sys, time

ROOT = pathlib.Path(__file__).resolve().parent
PERMS = tuple(permutations(range(3)))
IDENTITY = PERMS.index((0, 1, 2))
ACTS = tuple(product(range(6), repeat=3))
RELATIONS = tuple(range(512))
COUNTS = {}

def check(value, message):
    if not value:
        raise RuntimeError(message)

def done(name, n):
    COUNTS[name] = n

def seq(p, q):
    return PERMS.index(tuple(PERMS[q][PERMS[p][i]] for i in range(3)))

def inv(p):
    return PERMS.index(tuple(PERMS[p].index(i) for i in range(3)))

def transport_mask(p, q, mask):
    result = 0
    for x, y in product(range(3), repeat=2):
        if mask & (1 << (3*x+y)):
            result |= 1 << (3*PERMS[p][x]+PERMS[q][y])
    return result

MAPS = tuple(tuple(transport_mask(p, q, r) for r in RELATIONS)
             for p, q in product(range(6), repeat=2))

def tm(p, q, r):
    return MAPS[6*p+q][r]

def compose_mask(r, s):
    result = 0
    for x in range(3):
        row = (r >> (3*x)) & 7
        out = 0
        for y in range(3):
            if row & (1 << y):
                out |= (s >> (3*y)) & 7
        result |= out << (3*x)
    return result

COMP = tuple(tuple(compose_mask(r, s) for s in RELATIONS) for r in RELATIONS)
DELTA = 1 + 16 + 256

def relation_tests():
    n = 0
    for p, q, r in product(range(6), range(6), RELATIONS):
        a = tm(p, q, r)
        check(tm(inv(p), inv(q), a) == r, 'inverse relation action')
        check(tm(IDENTITY, IDENTITY, r) == r, 'identity relation action')
        n += 1
    done('all_relation_identity_inverse', n)
    n = 0
    for p, q, u, v in product(range(6), repeat=4):
        lhsmap, rhsmap = MAPS[6*u+v], MAPS[6*seq(p,u)+seq(q,v)]
        first = MAPS[6*p+q]
        for r in RELATIONS:
            check(lhsmap[first[r]] == rhsmap[r], 'composite relation action')
            n += 1
    done('all_relation_composite', n)
    # All 512^2 pairs and all six middle bijections; endpoint permutations
    # checked separately. Combined these generate every (S3)^3 action.
    n = 0
    for p in range(6):
        left = MAPS[6*IDENTITY+p]
        right = MAPS[6*p+IDENTITY]
        for r in RELATIONS:
            row, movedrow = COMP[r], COMP[left[r]]
            for s in RELATIONS:
                check(row[s] == movedrow[right[s]], 'middle witness cancellation')
                n += 1
    done('all_relation_pairs_middle_permutations', n)
    n = 0
    for p in range(6):
        left = MAPS[6*p+IDENTITY]
        right = MAPS[6*IDENTITY+p]
        for r in RELATIONS:
            row, leftrow = COMP[r], COMP[left[r]]
            for s in RELATIONS:
                check(left[row[s]] == leftrow[s], 'source naturality')
                check(right[row[s]] == row[right[s]], 'target naturality')
                n += 2
    done('all_relation_pairs_endpoint_permutations', n)
    for p in range(6):
        check(tm(p,p,DELTA) == DELTA, 'diagonal action')
    done('diagonal_actions', 6)

@dataclass(frozen=True)
class Cell:
    a: int
    b: int
    mask: int
    def move(self, action):
        return Cell(self.a, self.b, tm(action[self.a], action[self.b], self.mask))

@dataclass(frozen=True)
class Tree:
    kind: str
    args: tuple


def L(c): return Tree('leaf', (c,))
def U(a): return Tree('unit', (a,))
def B(t,u,k=0):
    check(normal(t).out.b == normal(u).out.a, 'binary endpoint typing')
    return Tree('binary', (k,t,u))
def D(k,t): return Tree('decoration', (k,t))

@dataclass(frozen=True)
class Flat:
    out: Cell
    profile: tuple[Cell, ...]
    value: int
    def move(self, p):
        return Flat(self.out.move(p), tuple(c.move(p) for c in self.profile), self.value)

@lru_cache(None)
def normal(t):
    if t.kind == 'leaf':
        c, = t.args
        return Flat(c,(c,),0)
    if t.kind == 'unit':
        a, = t.args
        return Flat(Cell(a,a,DELTA),(),0)
    if t.kind == 'decoration':
        k,u = t.args
        x = normal(u)
        return Flat(x.out,x.profile,k ^ x.value)
    k,u,v = t.args
    x,y = normal(u),normal(v)
    return Flat(Cell(x.out.a,y.out.b,COMP[x.out.mask][y.out.mask]),
                x.profile+y.profile,k ^ x.value ^ y.value)

def move(t,p):
    if t.kind == 'leaf': return L(t.args[0].move(p))
    if t.kind == 'unit': return t
    if t.kind == 'decoration': return D(t.args[0],move(t.args[1],p))
    k,u,v = t.args
    return B(move(u,p),move(v,p),k)

def pairs(mask):
    return {(x,y) for x,y in product(range(3),repeat=2) if mask & (1 << (3*x+y))}

def independent(t):
    """Independent set-composition evaluator, not COMP lookup or normal()."""
    if t.kind == 'leaf':
        c, = t.args
        return c.a,c.b,pairs(c.mask),(c,),0
    if t.kind == 'unit':
        a, = t.args
        return a,a,{(i,i) for i in range(3)},(),0
    if t.kind == 'decoration':
        k,u = t.args
        a,b,r,prof,n = independent(u)
        return a,b,r,prof,(k+n)%2
    k,u,v = t.args
    a,b,r,p,m = independent(u)
    bb,c,s,q,n = independent(v)
    check(b == bb,'independent typing')
    rs = {(x,z) for x,y in r for yy,z in s if y == yy}
    return a,c,rs,p+q,(k+m+n)%2

def graft(t, replacements):
    values = iter(replacements)
    def go(u):
        if u.kind == 'leaf':
            v = next(values)
            check(normal(v).out == u.args[0], 'graft output type')
            return v
        if u.kind == 'unit': return u
        if u.kind == 'decoration': return D(u.args[0],go(u.args[1]))
        k,l,r=u.args
        return B(go(l),go(r),k)
    result=go(t)
    check(next(values,None) is None,'extra occurrence replacement')
    return result

def subst(outer, forest):
    check(len(forest) == len(outer.profile), 'forest occurrence cardinality')
    profile=[]
    value=outer.value
    for c,inner in zip(outer.profile,forest):
        check(c == inner.out,'forest typed occurrence')
        profile.extend(inner.profile)
        value ^= inner.value
    return Flat(outer.out,tuple(profile),value)

def compose_forest(first,second):
    ans=[]; offset=0
    for f in first:
        n=len(f.profile)
        ans.append(subst(f,second[offset:offset+n]))
        offset+=n
    check(offset == len(second),'forest composition covers each occurrence')
    return tuple(ans)

def tree_equation_refinement_tests():
    masks=(0,1,10,DELTA,511)
    samples=[]; equations=[]
    for a,b,c,d in product(range(3),repeat=4):
        for i,j,k in product(range(len(masks)),repeat=3):
            # All 81 interface chains and a deterministic representative mask basis.
            if (i+j+k)%5: continue
            u=L(Cell(a,b,masks[i]));v=L(Cell(b,c,masks[j]));w=L(Cell(c,d,masks[k]))
            samples.extend((B(B(u,v),w),B(u,B(v,w)),D(1,B(u,v))))
            equations.append(('R',B(B(u,v),w),B(u,B(v,w))))
            equations.append(('UL',B(U(a),u),u))
            equations.append(('UR',B(u,U(b)),u))
            equations.append(('D0',D(0,u),u))
            for m,n in product(range(2),repeat=2):
                equations.append(('DA',D(m,D(n,u)),D(m^n,u)))
            for m in range(2):
                equations.append(('DL',B(D(m,u),v),D(m,B(u,v))))
                equations.append(('DR',B(u,D(m,v)),D(m,B(u,v))))
    samples=tuple(dict.fromkeys(samples))
    for t in samples:
        f=normal(t); a,b,r,p,n=independent(t)
        check((f.out.a,f.out.b,pairs(f.out.mask),f.profile,f.value)==(a,b,r,p,n),
              'independent full flat evaluator')
    done('independent_tree_flat_evaluations',len(samples))
    equation_counts={name:0 for name in ('R','UL','UR','D0','DA','DL','DR')}
    for name,t,u in equations:
        check(normal(t)==normal(u),'full witness equation '+name)
        equation_counts[name]+=1
    for name,n in equation_counts.items(): done('equation_'+name,n)
    # Entire 216-element interface action checked on each canonical equation
    # instance at one fully mixed endpoint chain; arbitrary chains above check typing.
    # 300 equations for repeated A-A-A-A and 300 for mixed A-B-C-A.
    per_chain=300
    mixed_chain=15  # lexicographic (a,b,c,d) = (0,1,2,0)
    focused=equations[:per_chain]+equations[mixed_chain*per_chain:(mixed_chain+1)*per_chain]
    count=0
    for p in ACTS:
        for name,t,u in focused:
            check(normal(move(t,p))==normal(move(u,p)),'transport equation '+name)
            check(normal(move(t,p))==normal(t).move(p),'equivariant evaluation')
            count+=1
    done('all_216_actions_equation_and_semantics',count)
    delta=Cell(0,0,DELTA); repeated=B(L(delta),L(delta))
    # Same source and same target; genuinely parallel semantic refinement arrows.
    f00=(normal(D(0,L(delta))),normal(D(0,L(delta))))
    f11=(normal(D(1,L(delta))),normal(D(1,L(delta))))
    check(f00!=f11,'retained parallel arrow tuples differ')
    check(subst(normal(repeated),f00)==subst(normal(repeated),f11),
          'equal total does not identify arrows')
    # Repeated leaf occurrences really are independent, even when types coincide.
    left=(D(1,L(delta)),L(delta));right=(L(delta),D(1,L(delta)))
    check(graft(repeated,left)!=graft(repeated,right),'repeated occurrences collapsed')
    for p in ACTS:
        check(tuple(x.move(p) for x in f00)!=tuple(x.move(p) for x in f11),
              'transport preserves arrow distinction')
        for forest in (left,right):
            check(move(graft(repeated,forest),p)==graft(move(repeated,p),tuple(move(x,p) for x in forest)),
                  'literal transport-graft law')
        for f in (f00,f11):
            check(subst(normal(repeated),f).move(p)==
                  subst(normal(repeated).move(p),tuple(x.move(p) for x in f)),
                  'refinement endpoint transport')
    done('all_216_actions_repeated_and_parallel_arrows',len(ACTS))
    # Nontrivial three-layer forest composition, including a nullary insertion.
    first=tuple(normal(x) for x in (B(L(delta),L(delta)),D(1,L(delta))))
    second=tuple(normal(x) for x in (U(0),D(1,L(delta)),B(L(delta),L(delta))))
    third=tuple(normal(x) for x in (D(1,L(delta)),U(0),D(1,L(delta))))
    check(compose_forest(compose_forest(first,second),third)==
          compose_forest(first,compose_forest(second,third)),'forest associativity')
    for p in ACTS:
        check(tuple(x.move(p) for x in compose_forest(first,second))==
              compose_forest(tuple(x.move(p) for x in first),tuple(x.move(p) for x in second)),
              'transport forest composition')
    done('all_216_actions_forest_composition',len(ACTS))
    identities=tuple(normal(L(c)) for c in normal(repeated).profile)
    check(subst(normal(repeated),identities)==normal(repeated),'refinement identity')
    # Quotient by object orbit forgets a whole nontrivial stabilizer on U(A).
    stable=[p for p in ACTS if move(U(0),p)==U(0)]
    check(len(stable)==216,'nullary stabilizer unexpectedly lost')
    done('unit_object_stabilizer_size',len(stable))
    # Declared alpha=gamma equation is not invariant under alpha/beta swap.
    flip={'alpha':'beta','beta':'alpha','gamma':'gamma'}
    cls={'alpha':0,'gamma':0,'beta':1}
    check(cls['alpha']==cls['gamma'] and cls[flip['alpha']]!=cls[flip['gamma']],
          'noninvariant relation control')
    done('noninvariant_relation_no_descent',1)
    # Mutation-sensitive controls: require an actual counterexample to each mutant.
    check(any(seq(p,q)!=seq(q,p) for p,q in product(range(6),repeat=2)),
          'wrong action order mutation survived')
    check(any(tm(p,q,COMP[1][1])!=COMP[1][1] for p,q in product(range(6),repeat=2)),
          'rename only output mutation survived')
    check(graft(repeated,left)!=graft(repeated,(left[0],left[0])),
          'deduplicate repeated slots mutation survived')
    check(f00!=f11 and subst(normal(repeated),f00)==subst(normal(repeated),f11),
          'replace arrow by endpoint equality mutation survived')
    done('detected_mutations',4)

def main():
    start=time.monotonic()
    relation_tests()
    tree_equation_refinement_tests()
    result={'status':'PASS','evidence_class':'C; finite Python computation, not L',
            'finite_domain':{'interfaces':3,'points_per_interface':3,'permutations_per_interface':6,
                             'group_actions':216,'relations_per_endpoint_pair':512,
                             'witness_monoid':'Z/2'},
            'counts':COUNTS,'elapsed_seconds':round(time.monotonic()-start,3),
            'python':sys.version,'source_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()}
    print(json.dumps(result,indent=2,sort_keys=True))
    (ROOT/'finite_results.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')

if __name__=='__main__': main()
