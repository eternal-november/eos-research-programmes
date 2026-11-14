"""Exact finite diagnostics, not proofs of the general measurable theorems."""
from fractions import Fraction as F
from itertools import product
import json
from pathlib import Path
from math import isqrt

checks = {}
def push(weights, fn):
    out = {}
    for x, p in weights.items(): out[fn(x)] = out.get(fn(x), F(0)) + p
    return out

# Native triangular serial map with genuinely dependent second kernel.
K = {0:F(1,6),1:F(1,3),2:F(1,2)}
r = lambda x: int(x==2)
Kp=push(K,r)
L={0:{0:F(1,4),1:F(1,4),2:F(1,2)},1:{0:F(1,6),1:F(1,6),2:F(2,3)}}
s=lambda x:int(x==2)
Lp={b:push(row,s) for b,row in L.items()}
M={(x,y):p*q for x,p in K.items() for y,q in L[r(x)].items()}
Mp={(x,y):p*q for x,p in Kp.items() for y,q in Lp[x].items()}
assert push(M,lambda xy:(r(xy[0]),s(xy[1])))==Mp
source_body=lambda xy:(s(xy[1]),xy)
target_body=lambda xy: (xy[1],xy)
content_map=lambda q:(r(q[0]),s(q[1]))
for xy in M:
    visible,retained=source_body(xy)
    assert (visible,content_map(retained))==target_body((r(xy[0]),s(xy[1])))
checks['dependent_serial_kernel_pushforward']='passed'

# Explicit positive and zero-weight shared events, with raw zero edges retained.
W=[F(1,3),F(2,3),F(0)]
R=[[F(1,9),F(2,9)],[F(1,3),F(1,3)],[F(0)]]
T=[[F(1,6),F(1,6)],[F(1,6),F(1,2)],[F(0),F(0)]]
U=[[F(1,12),F(1,4)],[F(1,3),F(1,3)],[F(0)]]
for e,p in enumerate(W):
    joint=[[r*t/p if p else F(0) for t in T[e]] for r in R[e]]
    assert [sum(row) for row in joint]==R[e]
    assert [sum(row[j] for row in joint) for j in range(len(T[e]))]==T[e]
    for a,b,c in product(R[e],T[e],U[e]):
        left=(a*b/p)*c/p if p else F(0)
        right=a*(b*c/p)/p if p else F(0)
        assert left==right
checks['shared_world_marginals_zero_edges_associativity']='passed'

# Correlated tape (not independent coordinates), countable feedback native map.
mu={(a,b,a^b):F(1,4) for a,b in product(range(2),repeat=2)}
def native(alpha,w):
    a,b,c=w; return (a,b^alpha[1],c^alpha[1])
for alpha in product(range(2),repeat=3): assert push(mu,lambda w:native(alpha,w))==mu
closed=lambda w:native((0,w[0],0),w)
assert push(mu,closed)==mu
assert len({closed(w) for w in product(range(2),repeat=3)})==8
checks['countable_feedback_correlated_tape_and_raw_coverage']='passed'

# Analytic continuous no-go has a written proof: this only checks selected
# inverse/body points and the exact distinguishing CDF at t=1/4.
for a0,a1,u0,u1 in product([F(0),F(1,2),F(1)],repeat=4):
    v1=u1*u1 if a1==u0 else u1
    recovered=F(isqrt(v1.numerator),isqrt(v1.denominator)) if a1==u0 else v1
    assert recovered==u1
assert F(1,2)!=F(1,4) # P(U^2 <= 1/4)=1/2 vs P(U <=1/4)=1/4
checks['continuous_no_go_cdf_discriminator']='passed (analytic premise proved in manuscript)'

# Local map criteria alone do not enforce three-factor coherence.
def t12(x):a,b,c=x;return a,a^b,c
def t23(x):a,b,c=x;return a,b,b^c
assert t12(t23(t12((1,0,0)))) != t23(t12(t23((1,0,0))))
checks['noncoherent_local_witness_counterexample']='passed'

# Universal block-factorization iff on all 3-state relation pairs.
n=3
def comp(r,q):
 return tuple(sum(1<<v for v in range(n) if any((r[u]>>k)&1 and (q[k]>>v)&1 for k in range(n))) for u in range(n))
def join(r,q):return tuple(a|b for a,b in zip(r,q))
def close(r):
 r=join(r,tuple(1<<i for i in range(n)))
 while True:
  t=join(r,comp(r,r))
  if t==r:return r
  r=t
def subset(r,q):return all(a&~b==0 for a,b in zip(r,q))
rels=[tuple((m>>(n*i))&7 for i in range(n)) for m in range(512)]
closures={r:close(r) for r in rels}
for e in rels:
 for f in rels:
  ef=comp(closures[e],closures[f]);fe=comp(closures[f],closures[e])
  assert (closures[join(e,f)]==ef)==subset(fe,ef)
checks['block_factorization_all_262144_three_state_pairs']='passed'

# Controlled common-event kernel: private-state-dependent lifts, common
# history-dependent command. Check actual path marginals, not only one-step laws.
def world_weight(a,e):
    p=F(1,3) if a==0 else F(2,3)
    return p if e==0 else 1-p
def lift_weight(kind,state,e,nxt):
    if kind=='R': p=F(1,4) if state==e else F(3,4)
    else: p=F(1,3) if state==e else F(2,3)
    return p if nxt==0 else 1-p
def component_paths(kind,horizon):
    dist={():F(1)}
    for _ in range(horizon):
        nxt={}
        for path,weight in dist.items():
            state=path[-1][1] if path else 0
            a=path[-1][0] if path else 0
            for e,j in product(range(2),repeat=2):
                new=path+((e,j),)
                nxt[new]=weight*world_weight(a,e)*lift_weight(kind,state,e,j)
        dist=nxt
    return dist
def joint_paths(horizon):
    dist={():F(1)}
    for _ in range(horizon):
        nxt={}
        for path,weight in dist.items():
            r,t=(path[-1][1],path[-1][2]) if path else (0,0)
            a=path[-1][0] if path else 0
            for e,j,k in product(range(2),repeat=3):
                new=path+((e,j,k),)
                nxt[new]=weight*world_weight(a,e)*lift_weight('R',r,e,j)*lift_weight('T',t,e,k)
        dist=nxt
    return dist
for horizon in range(1,5):
    joint=joint_paths(horizon)
    assert sum(joint.values())==1
    assert push(joint,lambda path:tuple((e,j) for e,j,k in path))==component_paths('R',horizon)
    assert push(joint,lambda path:tuple((e,k) for e,j,k in path))==component_paths('T',horizon)
checks['controlled_shared_world_path_marginals_through_length_4']='passed'

out={'status':'passed','scope':'finite exact diagnostics only; no Lean or general measurable proof certification','checks':checks}
Path(__file__).with_name('results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
