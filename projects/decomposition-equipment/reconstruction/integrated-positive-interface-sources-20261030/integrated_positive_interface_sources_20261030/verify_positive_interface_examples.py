#!/usr/bin/env python3
"""Exact rational sanity checks. No Monte Carlo; not a formal/general proof."""
from fractions import Fraction as F
from itertools import product
from math import comb
import json
from pathlib import Path


def mat(rows): return [[F(x) for x in row] for row in rows]
def mm(A,B): return [[sum(a*b for a,b in zip(row,col)) for col in zip(*B)] for row in A]
def mv(A,x): return [sum(a*b for a,b in zip(row,x)) for row in A]
def eye(n): return mat([[int(i==j) for j in range(n)] for i in range(n)])
def basis(n,j): return [F(i==j) for i in range(n)]
def positive(A): return all(x>=0 for row in A for x in row)
def normalized(instruments):
    n=len(instruments[0][0])
    return all(sum(M[i][j] for M in instruments for i in range(len(M)))==1 for j in range(n))
def permutation(targets):
    return mat([[int(i==targets[j]) for j in range(len(targets))] for i in range(len(targets))])

# No equivariant section into the original carrier, but a positive quotient.
Q=mat([[1,1,0],[0,0,1]])
T=permutation([0,1,0]); U=permutation([0,1,1]); A=mat([[1,1],[0,0]])
assert mm(Q,T)==mm(A,Q)==mm(Q,U)
# A section maps B to b and A to lambda*a1+(1-lambda)*a2.
# T at B forces lambda=1; U at B forces lambda=0.
required_lambda_T=F(1); required_lambda_U=F(0)
assert required_lambda_T!=required_lambda_U

# Positive instrument quotient: four square vertices plus a redundant midpoint.
# Instrument read outputs reset to the 00 state in this standalone algebraic
# fixture. This is NOT an experimental reset permission in the theorem.
Q=mat([[1,1,1,1,1],[0,0,1,1,F(1,2)],[0,1,0,1,F(1,2)]])
V=[r[:4] for r in Q]
Cdiag=[row+[F(1,2) if i in (0,3) else F(0)] for i,row in enumerate(eye(4))]
Coff=[row+[F(1,2) if i in (1,2) else F(0)] for i,row in enumerate(eye(4))]
assert mm(V,Cdiag)==Q==mm(V,Coff)
ops=[]
for axis in (1,2):
    raw=[]; abstract=[]
    for bit in (0,1):
        effects=[v if bit else 1-v for v in Q[axis]]
        K=[effects]+[[F(0)]*5 for _ in range(4)]
        H=[effects[:4]]+[[F(0)]*4 for _ in range(3)]
        L=[[F(0)]*3 for _ in range(3)]
        L[0][axis]=F(1 if bit else -1)
        if not bit: L[0][0]=1
        assert positive(K) and positive(H)
        assert mm(Q,K)==mm(L,Q)
        assert mm(V,H)==mm(L,V)
        ops.append((K,H)); raw.append(K); abstract.append(H)
    assert normalized(raw) and normalized(abstract)
for targets,L in [([0,2,1,3,4],mat([[1,0,0],[0,0,1],[0,1,0]])),
                  ([2,3,0,1,4],mat([[1,0,0],[1,-1,0],[0,0,1]]))]:
    K=permutation(targets); H=permutation(targets[:4])
    assert mm(Q,K)==mm(L,Q) and mm(V,H)==mm(L,V)
    assert normalized([K]) and normalized([H]); ops.append((K,H))
word_count=0; state_lift_checks=0
for length in range(5):
    for word in product(range(len(ops)),repeat=length):
        word_count+=1
        for j in range(5):
            p=basis(5,j)
            for C in (Cdiag,Coff):
                eta=mv(C,p); pp=p[:]
                for k in word:
                    K,H=ops[k]; pp=mv(K,pp); eta=mv(H,eta)
                assert mv(Q,pp)==mv(V,eta)
                assert sum(pp)==sum(eta)
                state_lift_checks+=1

# Same one-bit marginals, different joint behavior, and no affine section.
plus=[F(1,2),F(0),F(0),F(1,2)]
minus=[F(0),F(1,2),F(1,2),F(0)]
assert mv(V,plus)==mv(V,minus)==[F(1),F(1,2),F(1,2)]
assert plus[3]!=minus[3]
assert [V[i][0]+V[i][3] for i in range(3)]==[V[i][1]+V[i][2] for i in range(3)]
assert [basis(4,0)[i]+basis(4,3)[i] for i in range(4)] != [basis(4,1)[i]+basis(4,2)[i] for i in range(4)]

# Explicit bounded-stop job interpreter. Warning arrives immediately; gate
# decision latency is g<L, load arrives L ticks later, and cutoff commands disable.
# Each completed branch drains because f,b>=L. Safe-completion, not collision
# probability alone, is the event compared with the coefficient formula.
outcomes=((0,0),(0,1),(1,0),(1,1))
def interpret(seq,T,f,b,L,g=F(1,2)):
    assert 0<g<L<=f<b
    now=0; done=0; hazard=False
    for x,y in seq:
        if now>=T: break
        duration=f if x==0 else b
        load=now+L; end=now+duration
        if x==0 and y==1 and now+g<=load<=min(end,T+g): hazard=True
        if end>T:
            now=T; break
        now=end; done+=1
    finish=min(now,T)+L  # conservative final drain, even if already drained
    assert finish<=T+L
    return done==len(seq) and now<=T and not hazard

def coefficient(p,n,T,f,b):
    if T<n*f: return F(0)
    k=min(n,(T-n*f)//(b-f))
    return sum(F(comb(n,j))*p[0]**(n-j)*(p[2]+p[3])**j for j in range(k+1))

def enumerated(p,n,T,f,b,L):
    total=F(0); norm=F(0)
    for ids in product(range(4),repeat=n):
        prob=F(1)
        for i in ids: prob*=p[i]
        norm+=prob
        if interpret([outcomes[i] for i in ids],T,f,b,L): total+=prob
    assert norm==1
    return total
laws=[(F(9,10),F(0),F(0),F(1,10)),
      (F(4,5),F(1,10),F(1,10),F(0)),
      (F(1,4),)*4,
      (F(1,7),F(2,7),F(3,7),F(1,7))]
job_checks=0; enumerated_words=0
for n in range(1,6):
    for T in range(0,5*n+2):
        for p in laws:
            assert coefficient(p,n,T,2,5)==enumerated(p,n,T,2,5,1)
            job_checks+=1; enumerated_words+=4**n
n10=[]
for label,p in zip(('positive_dependence','negative_dependence'),laws[:2]):
    s=coefficient(p,10,29,2,5)
    n10.append({'law':label,'safe_timely_probability':str(s),'decimal':float(s)})
assert n10[0]['safe_timely_probability']!=n10[1]['safe_timely_probability']
result={
 'arithmetic':'exact fractions',
 'equivariant_section_counterexample':'PASS: incompatible lambda=1 and lambda=0',
 'positive_instrument_quotient':{'result':'PASS','operators':len(ops),'words_through_length_4':word_count,'raw_state_and_lift_checks':state_lift_checks,'raw_states':5,'positive_abstract_states':4},
 'square_partial_context_and_no_affine_section':'PASS',
 'job_formula_vs_bounded_interpreter':{'result':'PASS','laws':len(laws),'n_range':[1,5],'deadline_checks':job_checks,'weighted_source_words_enumerated':enumerated_words,'f':2,'b':5,'L':1,'gate_latency':'1/2','cutoff_and_final_drain':'All interpreted paths finish by T+L'},
 'n10_T29_examples':n10,
 'scope':'Finite exact sanity checks only. No proof of general theorem, concentration, physical gate/drain premises, capability compiler or categorical comparisons.'
}
# Partial-pair evidence fixture: W, Y_fast, Y_slow genuinely coexist, but each
# operational branch exposes only W and one routed load. Distinct STRICTLY
# positive three-bit laws have identical two permitted pair marginals.
triple_outcomes=tuple(product((0,1),repeat=3))
def triple_law(coupling_fraction):
    law={}
    for w,pw,qf,qs in ((0,F(4,5),F(1,10),F(1,5)),(1,F(1,5),F(3,10),F(1,20))):
        c=min(qf,qs)*coupling_fraction
        conditional={(0,0):1-qf-qs+c,(0,1):qs-c,(1,0):qf-c,(1,1):c}
        for (yf,ys),mass in conditional.items(): law[(w,yf,ys)]=pw*mass
    assert sum(law.values())==1 and all(x>0 for x in law.values())
    return law

def marginal(law,coords):
    ans={}
    for outcome,prob in law.items():
        key=tuple(outcome[i] for i in coords)
        ans[key]=ans.get(key,F(0))+prob
    return ans

triple1,triple2=triple_law(F(1,3)),triple_law(F(2,3))
assert triple1!=triple2
for coords in ((0,1),(0,2)):
    assert marginal(triple1,coords)==marginal(triple2,coords)
route_checks=0
for route in product((1,2),repeat=2):
    distributions=[]
    for law in (triple1,triple2):
        dist={}
        for outcome,prob in law.items():
            w=outcome[0]; key=(w,outcome[route[w]])
            dist[key]=dist.get(key,F(0))+prob
        distributions.append(dist)
    assert distributions[0]==distributions[1]; route_checks+=1
# Canonical routing W=0 fast, W=1 slow gives safe masses a,b.
a=sum(p for (w,yf,ys),p in triple1.items() if w==0 and yf==0)
bm=sum(p for (w,yf,ys),p in triple1.items() if w==1 and ys==0)
assert (a,bm)==(F(18,25),F(19,100))
def triple_success(seq,T):
    duration=0
    for w,yf,ys in seq:
        duration += 2 if w==0 else 5
        if (yf if w==0 else ys)==1: return False
    return duration<=T
triple_job_checks=0
for n in range(1,4):
    for T in range(0,5*n+1):
        predicted=F(0) if T<2*n else sum(F(comb(n,j))*a**(n-j)*bm**j for j in range(min(n,(T-2*n)//3)+1))
        for law in (triple1,triple2):
            actual=F(0)
            for seq in product(triple_outcomes,repeat=n):
                prob=F(1)
                for z in seq: prob*=law[z]
                if triple_success(seq,T): actual+=prob
            assert actual==predicted; triple_job_checks+=1
both1=sum(p for (w,yf,ys),p in triple1.items() if yf==ys==1)
both2=sum(p for (w,yf,ys),p in triple2.items() if yf==ys==1)
assert both1!=both2
result['partial_pair_three_bit_fixture']={
 'result':'PASS','strictly_positive_distinct_laws':2,
 'identical_pair_marginals':['W,Y_fast','W,Y_slow'],
 'one_route_selection_maps_checked':route_checks,
 'job_formula_checks_n1_to_3':triple_job_checks,
 'safe_fast_mass':str(a),'safe_slow_mass':str(bm),
 'both_loads_one_probability':[str(both1),str(both2)],
 'scope':'Reading/using both loads is a different context; its law is not determined by the pair evidence.'
}
# Exact Section H correlated/exclusive example and its normalized gluing.
r=F(1,100); pw={0:F(9,10),1:F(1,10)}
correlated={}; exclusive={}
for w in (0,1):
    for f,slow in product((0,1),repeat=2):
        correlated[(w,f,slow)]=pw[w]*({(0,0):1-r,(1,1):r}.get((f,slow),F(0)))
        exclusive[(w,f,slow)]=pw[w]*({(0,0):1-2*r,(1,0):r,(0,1):r}.get((f,slow),F(0)))
pF=marginal(correlated,(0,1)); pS=marginal(correlated,(0,2))
assert pF==marginal(exclusive,(0,1)) and pS==marginal(exclusive,(0,2))
glued={(w,f,slow):pF[(w,f)]*pS[(w,slow)]/pw[w] for w,f,slow in triple_outcomes}
assert sum(glued.values())==1 and all(x>=0 for x in glued.values())
assert marginal(glued,(0,1))==pF and marginal(glued,(0,2))==pS
sa=F(9,10)*(1-r); sb=F(1,10)*(1-r)
s10=sum(F(comb(10,j))*sa**(10-j)*sb**j for j in range(4))
assert s10==(1-r)**10*coefficient(laws[0],10,29,2,5)
union=[sum(prob for (w,f,slow),prob in law.items() if f or slow) for law in (correlated,exclusive,glued)]
assert union==[r,2*r,2*r-r*r]
result['section_H_correlated_exclusive']={
 'result':'PASS','warning_probability':'1/10','load_probability':str(r),
 'both_pair_marginals':'identical for correlated, exclusive and glued laws',
 'positive_joint_extension':'normalized and exact pair marginals',
 'n10_k3_success':str(s10),'n10_k3_success_decimal':float(s10),
 'both_route_union_risk_correlated_exclusive_glued':[str(x) for x in union],
 'scope':'Exact Section H example; paired probes leave cross-route correlation unidentified.'
}
if __name__=='__main__':
    Path(__file__).with_name('positive_interface_example_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
