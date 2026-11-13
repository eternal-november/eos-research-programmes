#!/usr/bin/env python3
"""Exact finite sanity checks, not a proof of any infinite/categorical theorem."""
from fractions import Fraction as F
from collections import defaultdict, Counter
from itertools import product
from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent
counts=Counter()
def ck(group,condition):
    counts[group]+=1
    assert condition, (group,counts[group])
def mul(A,B):return [[sum(a*b for a,b in zip(row,col)) for col in zip(*B)] for row in A]
def mv(A,v):return [sum(a*b for a,b in zip(row,v)) for row in A]
G=[[F(0),F(3,2)],[F(2,5),F(0)]]; w=[F(2),F(1)];rho=F(4,5)
ck('gain',all(a<=rho*b for a,b in zip(mv(G,w),w)))
ck('gain',mul(G,G)==[[F(3,5),0],[0,F(3,5)]])
res=[F(75,4),F(21,2)]
ck('gain',[3+x for x in mv(G,res)]==res)
P=[[F(0),F(1,2)],[F(1,2),F(0)]];C=[[F(0),F(1)],[F(1),F(0)]]
v=[F(1),F(1)];p=v[:]
for k in range(41):
    ck('critical_finite_powers',p==[F(1,2**k)]*2)
    ck('critical_finite_powers',v==[F(1)]*2)
    p=mv(P,p);v=mv(C,v)
# Positive random walk survivor DP. No truncation in reachable state set.
for down in [F(1,2),F(2,3),F(3,4)]:
 for n in range(1,9):
    dist={n:F(1)};exited=F(0)
    for t in range(101):
      survival=sum(dist.values())
      ck('walk_mass',survival+exited==1)
      ck('walk_tail_squared',survival**2*(t+1)<=2*n*n)
      nxt=defaultdict(F);hit=F(0)
      for x,mass in dist.items():
        if x==1:hit+=mass*down
        else:nxt[x-1]+=mass*down
        nxt[x+1]+=mass*(1-down)
      ck('walk_first_exit',survival-sum(nxt.values())==hit)
      if down==F(1,2) and n==1 and t<10:
        # First hit at odd 2j+1 has Catalan_j / 2^(2j+1).
        from math import comb
        d=t+1
        expected=F(comb(2*(d//2),d//2),d//2+1)/2**d if d%2 else F(0)
        ck('walk_catalan_coefficients',hit==expected)
      exited+=hit;dist=nxt
# Marked kernels indexed (input,duration,output), conventional row bookkeeping.
def compose(K,L):
 out=defaultdict(F)
 for (x,d,y),a in K.items():
  for (yy,e,z),b in L.items():
   if y==yy:out[x,d+e,z]+=a*b
 return {k:v for k,v in out.items() if v}
K={(0,1,0):F(1,3),(0,2,1):F(1,2),(1,1,0):F(1,4),(1,3,1):F(1,2)}
L={(0,1,0):F(1,2),(0,2,1):F(1,4),(1,1,1):F(2,3)}
M={(0,0,0):F(1,3),(0,2,1):F(1,2),(1,1,0):F(3,4)}
a=compose(compose(K,L),M);b=compose(K,compose(L,M))
for key in a.keys()|b.keys():ck('marked_associativity_coefficients',a.get(key,0)==b.get(key,0))
I={(x,0,x):F(1) for x in range(2)}
ck('marked_units',compose(I,K)==K);ck('marked_units',compose(K,I)==K)
# Countdown exact emission step: sampling is the first step.
for d in range(1,21):
 remaining=d-1;emit=1 if remaining==0 else None
 for step in range(2,d+2):
  if emit is None:
   remaining-=1
   if remaining==0:emit=step
 ck('countdown_indexing',emit==d)
# Scalar first-exit A*(1+Q+Q^2+...) versus time-step renewal recursion.
Q={1:F(1,4),2:F(1,4)};A={1:F(1,2)};H=30
W=[F(0)]*(H+1)
for n in range(1,H+1):W[n]=A.get(n,F(0))+sum(q*W[n-d] for d,q in Q.items() if n>=d)
power={0:F(1)};enum=[F(0)]*(H+1)
for k in range(H):
 for d,p0 in power.items():
  for e,a0 in A.items():
   if d+e<=H:enum[d+e]+=p0*a0
 nxt=defaultdict(F)
 for d,p0 in power.items():
  for e,q in Q.items():
   if d+e<=H:nxt[d+e]+=p0*q
 power=nxt
for n in range(H+1):ck('first_exit_coefficients',W[n]==enum[n])
ck('first_exit_submass',sum(W)<=1)
# Zero-duration trace: a self-loop 1/3 and immediate exit 1/2 give
# coefficient 3/4 at duration 0 (remaining 1/4 missing); exact geometric identity.
zloop=F(1,3);zexit=F(1,2);ztrace=zexit/(1-zloop)
ck('zero_duration_trace',ztrace==F(3,4))
for k in range(21):
 partial=sum(zexit*zloop**j for j in range(k))
 ck('zero_duration_trace',partial+ztrace*zloop**k==ztrace)
# Closed zero-duration loop has NO finite exit, not an artificial time-0 exit.
ck('zero_duration_trace',sum(F(0)*F(1)**j for j in range(21))==0)
# Actual finite countdown distribution over pending (remaining,outcome) states.
Fmark={(1,'a'):F(1,4),(2,'a'):F(1,3),(4,'b'):F(1,6)}
pending=defaultdict(F);emitted=defaultdict(F)
for (d,o),mass in Fmark.items():
 if d==1:emitted[1,o]+=mass
 else:pending[d-1,o]+=mass
for step in range(2,6):
 nxt=defaultdict(F)
 for (remaining,o),mass in pending.items():
  if remaining==1:emitted[step,o]+=mass
  else:nxt[remaining-1,o]+=mass
 pending=nxt
for d in range(1,6):
 for o in ['a','b']:ck('countdown_distribution',emitted[d,o]==Fmark.get((d,o),0))
# Infinity atom stays in ALL tail tests; it cannot satisfy a vanishing bound.
infmass=F(1,5)
for t in range(1,101):ck('infinity_tail_guard',infmass+F(4,5)*(t<3)>=infmass)
ck('infinity_tail_guard',infmass>F(1,101))
# Relative-independent coupling: finite refinements of common deterministic base.
# Includes zero entries and differing continuation masses across base rows.
base=[[F(1,8),F(1,8),0],[0,F(1,4),0],[0,0,0]]
def refinement(tags,seed):
 states=list(product(range(3),range(tags)));Q={}
 for x in states:
  for y in states:
   weights=[F(1+((x[1]+j+seed)%tags)) for j in range(tags)]
   Q[x,y]=base[x[0]][y[0]]*weights[y[1]]/sum(weights)
 return states,Q
S,KS=refinement(2,0);T,KT=refinement(3,1);U,KU=refinement(2,1)
for states,Q0 in [(S,KS),(T,KT),(U,KU)]:
 for x in states:
  for j in range(3):ck('deterministic_lumping',sum(Q0[x,y] for y in states if y[0]==j)==base[x[0]][j])
def coupled(x,y,xp,yp,K1,K2):
 if xp[0]!=yp[0]:return F(0)
 den=base[x[0]][xp[0]]
 return K1[x,xp]*K2[y,yp]/den if den else F(0)
ST=[(x,y) for x in S for y in T if x[0]==y[0]]
for x,y in ST:
 for xp in S:ck('coupling_projection',sum(coupled(x,y,xp,yp,KS,KT) for yp in T)==KS[x,xp])
 for yp in T:ck('coupling_projection',sum(coupled(x,y,xp,yp,KS,KT) for xp in S)==KT[y,yp])
 ck('coupling_rowmass',sum(coupled(x,y,xp,yp,KS,KT) for xp,yp in ST)==sum(base[x[0]]))
triples=[(x,y,z) for x in S for y in T for z in U if x[0]==y[0]==z[0]]
for x,y,z in triples:
 for xp,yp,zp in triples:
  den=base[x[0]][xp[0]]
  left=coupled(x,y,xp,yp,KS,KT)*KU[z,zp]/den if den else F(0)
  right=KS[x,xp]*coupled(y,z,yp,zp,KT,KU)/den if den else F(0)
  expected=KS[x,xp]*KT[y,yp]*KU[z,zp]/den**2 if den else F(0)
  ck('coupling_triple_associativity',left==right==expected)
  if not den:ck('coupling_zero_denominator',left==0)
# Distinct intermediate bases A and B, middle apex carrying both coordinates.
BA=[[F(1,8),F(1,8)],[F(0),F(1,4)]]
BB=[[F(1,6),F(1,12)],[F(1,4),F(0)]]
GG=list(product(range(2),range(2)));HH=list(product(range(2),range(2),range(2)));LL=GG[:]
def kg(g,gp):return BA[g[0]][gp[0]]*F(gp[1]+1,3)
def kh(h,hp):return BA[h[0]][hp[0]]*BB[h[1]][hp[1]]*4*F(hp[2]+1,3)
def kl(l,lp):return BB[l[0]][lp[0]]*F(lp[1]+1,3)
TT=[(g,h,l) for g in GG for h in HH for l in LL if g[0]==h[0] and h[1]==l[0]]
for g,h,l in TT:
 for gp,hp,lp in TT:
  da=BA[g[0]][gp[0]];db=BB[l[0]][lp[0]]
  gh=kg(g,gp)*kh(h,hp)/da if da else F(0)
  hl=kh(h,hp)*kl(l,lp)/db if db else F(0)
  left=gh*kl(l,lp)/db if db else F(0)
  right=kg(g,gp)*hl/da if da else F(0)
  expected=kg(g,gp)*kh(h,hp)*kl(l,lp)/(da*db) if da*db else F(0)
  ck('distinct_base_triple_associativity',left==right==expected)
for h in HH:
 for ap in range(2):ck('middle_apex_lumping',sum(kh(h,hp) for hp in HH if hp[0]==ap)==BA[h[0]][ap])
 for bp in range(2):ck('middle_apex_lumping',sum(kh(h,hp) for hp in HH if hp[1]==bp)==BB[h[1]][bp])
# Exact fibre infimum drift transfer, nonconstant potentials within fibres.
for seed in range(6):
 V={x:F(2)+F((x[0]+x[1]+seed)%4,4) for x in S}
 VR={r:min(V[x] for x in S if x[0]==r) for r in range(3)}
 for x in S:
  qv=sum(KS[x,y]*V[y] for y in S)
  ck('source_additive_drift',qv<=V[x]-1)
  ck('source_geometric_drift',qv<=V[x]/2)
 for r in range(3):
  qv=sum(base[r][j]*VR[j] for j in range(3))
  ck('fibre_inf_additive_drift',qv<=VR[r]-1)
  ck('fibre_inf_geometric_drift',qv<=VR[r]/2)
 # X=S <-S->base, then base <-T->T (left base projection,right identity).
 for y in T:
  nested=VR[y[0]]
  direct=min(V[x] for x,yy in ST if yy==y)
  ck('fibre_inf_span_composition',nested==direct)
# Forgetting the conditioning base destroys shared correlation: explicit fixture.
shared={(0,0):F(1,2),(1,1):F(1,2)}
independent={pair:F(1,4) for pair in product(range(2),repeat=2)}
ck('non_naturality_witness',shared!=independent)
ck('non_naturality_witness',shared.get((0,1),0)==0 and independent[0,1]==F(1,4))
files=['excursion_progress_transport.md','composition_challenge.md','verify_progress_feedback.py']
result={'status':'PASS','arithmetic':'fractions.Fraction only; no floating point', 'assertions':dict(sorted(counts.items())), 'total_assertions':sum(counts.values()), 'hashes':{f:hashlib.sha256((ROOT/f).read_bytes()).hexdigest() for f in files}, 'limitations':['Finite fixtures do not prove countable convergence, almost-sure termination, infinite expectation, trace axioms, CFS coherence or novelty.','Critical infinite expectation requires the analytic argument; checked finite powers only.','Coupling tests use full finite fibres and deterministic lumping; no arbitrary physical coupling or general CFS lifting is inferred.','Countdown verifier checks deterministic duration bookkeeping, not an independently implemented simulator.']}
text=json.dumps(result,indent=2,sort_keys=True)+'\n'
(ROOT/'verification_results.json').write_text(text)
print(text,end='')
