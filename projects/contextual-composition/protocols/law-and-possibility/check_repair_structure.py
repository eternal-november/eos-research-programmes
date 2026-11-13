#!/usr/bin/env python3
"""Exact finite regression checks for O7; not proofs of quantified theorems.

Python standard library only. Run from any directory; results written beside this
file. Probabilities use Fraction, never floating-point tolerances. Counts denote
explicit checked predicates (not independently proved mathematical theorems).
"""
from fractions import Fraction as F
from itertools import product
from collections import Counter, defaultdict
from pathlib import Path
import json

counts = Counter()
def check(group, predicate):
    counts[group] += 1
    if not predicate:
        raise AssertionError((group, counts[group]))

ZERO, ONE = (F(0), False), (F(1), True)
def add(a,b): return (a[0]+b[0], a[1] or b[1])
def mul(a,b): return (a[0]*b[0], a[1] and b[1])
def valid_e(a): return a[0]>=0 and (a[0]==0 or a[1])
def esum(xs):
    z=ZERO
    for x in xs: z=add(z,x)
    return z

# M stores only positive entries of its law, and an independently retained S.
def M(law, possible):
    law={x:F(p) for x,p in law.items() if p}
    possible=frozenset(possible)
    assert possible and set(law)<=possible
    assert all(p>0 for p in law.values()) and sum(law.values())==1
    return law,possible

def unit(x): return M({x:1},{x})
def bind(m,k):
    law=defaultdict(F)
    for x,p in m[0].items():
        for y,q in k(x)[0].items(): law[y]+=p*q
    return M(law, set().union(*(k(x)[1] for x in m[1])))
def fmap(m,f): return bind(m,lambda x:unit(f(x)))
def tensor(m,n): return bind(m,lambda x:bind(n,lambda y:unit((x,y))))

# Raw rows: (weight, present_flag, cost, public_body); every actual row is present.
def row(p,c,b): return (F(p),True,c,b)
def outcome(r): return r[2:]
def observe(rows):
    law=defaultdict(F)
    for p,b,c,t in rows:
        if b: law[(c,t)]+=p
    return M(law,{outcome(r) for r in rows if r[1]})
def canonical(rows):
    mu,S=observe(rows)
    return [row(mu.get(z,0),*z) for z in sorted(S)]
def native(src,tgt,f,exact=True,presence=True):
    if len(f)!=len(src) or any(j<0 or j>=len(tgt) for j in f): return False
    for i,r in enumerate(src):
        s=tgt[f[i]]
        if r[3]!=s[3] or (r[2]!=s[2] if exact else r[2]<s[2]): return False
    for j,s in enumerate(tgt):
        pre=[src[i] for i in range(len(src)) if f[i]==j]
        coeff=esum((r[0],r[1]) for r in pre)
        if coeff[0]!=s[0] or (presence and coeff[1]!=s[1]): return False
    return True

def collapse(rows):
    target=canonical(rows)
    index={outcome(r):j for j,r in enumerate(target)}
    return target,[index[outcome(r)] for r in rows]

# E including absent zero, present zero, and nonnormalized intermediate values.
grid=[ZERO,(F(0),True)]+[(p,True) for p in [F(1,3),F(1,2),F(1),F(2)]]
check('presence_distinction',ZERO!=(F(0),True))
for a in grid:
    check('semiring',add(a,ZERO)==a and mul(a,ONE)==a and mul(a,ZERO)==ZERO)
    for b in grid:
        check('semiring',valid_e(add(a,b)) and valid_e(mul(a,b)))
        check('semiring',add(a,b)==add(b,a) and mul(a,b)==mul(b,a))
        check('forgetful_rig',add(a,b)[0]==a[0]+b[0] and mul(a,b)[0]==a[0]*b[0])
        for c in grid:
            check('semiring',add(add(a,b),c)==add(a,add(b,c)))
            check('semiring',mul(mul(a,b),c)==mul(a,mul(b,c)))
            check('semiring',mul(a,add(b,c))==add(mul(a,b),mul(a,c)))

states=(0,1)
values=[]
for p in [F(0),F(1,2),F(1)]:
    for S in [{0},{1},{0,1}]:
        if {x for x,w in [(0,p),(1,1-p)] if w}<=S:
            values.append(M({0:p,1:1-p},S))
kernels=list(product(values,repeat=2))
for m in values:
    check('monad_units',bind(m,unit)==m)
    for kt in kernels:
        k=lambda x,kt=kt:kt[x]
        for x in states: check('monad_units',bind(unit(x),k)==k(x))
        for lt in kernels:
            l=lambda x,lt=lt:lt[x]
            check('monad_associativity',bind(bind(m,k),l)==bind(m,lambda x:bind(k(x),l)))
    for n in values:
        check('product',fmap(tensor(m,n),lambda xy:(xy[1],xy[0]))==tensor(n,m))
        check('product',tensor(m,n)[1]==frozenset(product(m[1],n[1])))
        for o in values:
            check('product',fmap(tensor(tensor(m,n),o),lambda z:(z[0][0],z[0][1],z[1]))==fmap(tensor(m,tensor(n,o)),lambda z:(z[0],z[1][0],z[1][1])))
    check('product',fmap(tensor(m,unit(None)),lambda z:z[0])==m)
# zero-probability possibilities survive dependent bind.
z=M({0:1},{0,1})
check('zero_bind',bind(z,lambda x:unit('good' if x==0 else 'ghost'))==M({'good':1},{'good','ghost'}))

# Families with duplicate positive atoms, duplicate zero atoms, and empty fibres forbidden.
raws=[]
for p in [F(0),F(1,3),F(1)]:
    for q in [F(0),F(1,2),F(1)]:
        raws.append([row(p*q,0,'a'),row(p*(1-q),0,'a'),row(1-p,1,'b'),row(0,2,'z'),row(0,2,'z')])
for H in raws:
    R,f=collapse(H)
    check('canonical_collapse',native(H,R,f) and set(f)==set(range(len(R))))
    check('canonical_collapse',observe(H)==observe(R))
    # Enumerate every carrier function into representative: exactly one native cell.
    check('reflection_uniqueness',sum(native(H,R,g) for g in product(range(len(R)),repeat=len(H)))==1)
    # Equal observation, distinct raw presentation by splitting each row.
    Q=[row(r[0]*s,r[2],r[3]) for r in H for s in [F(1,3),F(2,3)]]
    mu,_=observe(H)
    W=[]; fp=[]; fq=[]
    for i,r in enumerate(H):
        for j,s in enumerate(Q):
            if outcome(r)==outcome(s):
                mass=mu.get(outcome(r),F(0))
                W.append(row(r[0]*s[0]/mass if mass else 0,r[2],r[3]))
                fp.append(i); fq.append(j)
    check('two_sided_fibre_product',observe(H)==observe(Q))
    check('two_sided_fibre_product',native(W,H,fp) and native(W,Q,fq))
    check('two_sided_fibre_product',set(fp)==set(range(len(H))) and set(fq)==set(range(len(Q))))
    check('two_sided_fibre_product',any(r[0]==0 and r[3]=='z' for r in W))

# Old probability cell permits insertion of a zero-weight target ghost; E does not.
P=[row(1,0,'good')]; Q=P+[row(0,0,'bad')]
check('ghost_cell',native(P,Q,[0],presence=False))
check('ghost_cell',not native(P,Q,[0],presence=True))
check('asymmetric_separation',observe(P)[0]==observe(Q)[0])
relation=lambda x,y:x[1]==y[1] and x[0]<=y[0]
SP,SQ=observe(P)[1],observe(Q)[1]
check('asymmetric_separation',all(any(relation(x,y) for y in SQ) for x in SP))
check('asymmetric_separation',not all(any(relation(x,y) for x in SP) for y in SQ))
# Candidate-covered span exists, but no both-covered relation span: bad has no match.
check('asymmetric_separation',native(P,P,[0],exact=False,presence=False) and native(P,Q,[0],exact=True,presence=False))

# Conditional law lifting and zero fillers, genuinely unequal candidate/reference costs.
for p,q in product([F(0),F(1,3),F(1)],repeat=2):
    A=[row(p,0,'a'),row(1-p,0,'a'),row(0,1,'z'),row(0,1,'z')]
    B=[row(q,2,'a'),row(1-q,2,'a'),row(0,3,'z')]
    ma,sa=observe(A); mb,sb=observe(B)
    G={((0,'a'),(2,'a')):F(1)}
    W=[]; fa=[]; fb=[]
    for i,a in enumerate(A):
        for j,b in enumerate(B):
            x,y=outcome(a),outcome(b)
            g=G.get((x,y),F(0)); den=ma.get(x,0)*mb.get(y,0)
            mass=g*a[0]*b[0]/den if den else F(0)
            if mass:
                W.append(row(mass,b[2],b[3]));fa.append(i);fb.append(j)
    for i,a in enumerate(A):
        if i not in fa:
            j=next(j for j,b in enumerate(B) if relation(outcome(a),outcome(b)))
            W.append(row(0,B[j][2],B[j][3]));fa.append(i);fb.append(j)
    check('conditional_lift',native(W,A,fa,exact=False,presence=False))
    check('conditional_lift',native(W,B,fb,exact=True,presence=False))
    check('conditional_lift',set(fa)==set(range(len(A))))
    check('conditional_lift',sum(r[0] for r in W)==1)
    check('conditional_lift',all(relation(outcome(A[i]),outcome(B[j])) for i,j in zip(fa,fb)))

# Reconstruction lax comparison: independent tuples collapse, not an isomorphism.
H=[row(F(1,2),0,'id'),row(F(1,2),1,'id')]
HH=[row(a[0]*b[0],a[2]+b[2],'id') for a,b in product(H,repeat=2)]
R,f=collapse(HH)
check('lax_comparison',len(HH)==4 and len(R)==3 and len(set(f))==3)
check('lax_comparison',native(HH,R,f))
check('lax_comparison',dict(observe(R)[0])=={(0,'id'):F(1,4),(1,'id'):F(1,2),(2,'id'):F(1,4)})
# Both triple-collapse paths induce exactly the same raw-to-canonical map.
HHH=[row(a[0]*b[0]*c[0],a[2]+b[2]+c[2],'id') for a,b,c in product(H,repeat=3)]
RR,ff=collapse(HHH)
index={outcome(r):i for i,r in enumerate(RR)}
left=[index[(R[f[2*i+j]][2]+H[k][2],'id')] for i,j,k in product(range(2),repeat=3)]
right=[index[(H[i][2]+R[f[2*j+k]][2],'id')] for i,j,k in product(range(2),repeat=3)]
check('lax_coherence',left==right==ff and native(HHH,RR,ff))

result={'status':'passed','arithmetic':'fractions.Fraction (exact)',
        'scope':'Finite regression checks, not proofs of quantified categorical theorems.',
        'checks':dict(sorted(counts.items())), 'total_checked_predicates':sum(counts.values()),
        'finite_M_values':len(values),'finite_kernels':len(kernels),'raw_collapse_families':len(raws),
        'lax_example':{'composite_raw_rows':4,'canonical_rows':3},
        'negative_controls':['old ghost cell is not E-native','one-sided coverage does not imply both-sided coverage','canonical composition comparison is not invertible']}
Path(__file__).with_name('repair_structure_results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
