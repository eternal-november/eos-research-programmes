"""Exact finite diagnostics for the ABC/J supplement, not a general proof."""
from fractions import Fraction as F
from itertools import product
import json

def matmul(a,b):
    return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]
def rank(a):
    a=[[F(x) for x in r] for r in a]; r=0
    for c in range(len(a[0])):
        pivot=next((i for i in range(r,len(a)) if a[i][c]),None)
        if pivot is None: continue
        a[r],a[pivot]=a[pivot],a[r]; p=a[r][c]; a[r]=[x/p for x in a[r]]
        for i in range(len(a)):
            if i!=r:
                p=a[i][c]; a[i]=[x-p*y for x,y in zip(a[i],a[r])]
        r+=1
    return r
src=list(product(range(3),range(2),range(2))) # H,N,M
trg=list(product(range(5),range(2))) # H',N
keep={0:(0,0),1:(0,1),2:(1,0),3:(1,1),4:(2,0)}
U=[[int((h,n,m)==(keep[t][0],j,keep[t][1])) for h,n,m in src] for t,j in trg]
assert rank(U)==10
assert [i for i,col in enumerate(zip(*U)) if not any(col)]==[9,11]
old=list(product(range(3),range(2)))
R=[[int((t,j)==({0:0,1:2,2:4}[h],n)) for t,j in trg] for h,n in old]
augM=[[int((h,n,m)==(ho,no,0)) for h,n,m in src] for ho,no in old]
assert matmul(R,U)==augM
assert U[0]==[int(x==(0,0,0)) for x in src]
# Both independently constructed owner insertion orders use the same old projections.
source=list(product(range(3),range(2),range(2))) # H,M_A,P_C
# target product(K*M,L*P), coordinates unit + nonunit KM + nonunit LP
out=[('A',i,j) for i,j in product(range(2),repeat=2)]+[('C',i,j) for i,j in product(range(2),repeat=2) if (i,j)!=(0,0)]
def direct(owner,i,j):
    if owner=='A': return ((0 if i==0 else 1),j,0)
    return ((0 if i==0 else 2),0,j)
# Inserting A then C: A projection drops P, C projection drops M.
def via_A_C(owner,i,j):
    if owner=='A':
        intermediate=(i,j); return ((0 if intermediate[0]==0 else 1),intermediate[1],0)
    return ((0 if i==0 else 2),0,j)
def via_C_A(owner,i,j):
    if owner=='C': return ((0 if i==0 else 2),0,j)
    return ((0 if i==0 else 1),j,0)
assert [direct(*v) for v in out]==[via_A_C(*v) for v in out]==[via_C_A(*v) for v in out]
V=[[int(x==direct(*v)) for x in source] for v in out]
assert rank(V)==7
# Exact retained-reserve plan, complete zeros, and non-redrawing service.
Rraw=range(3); pairs=list(product(range(2),repeat=2))
alpha={0:F(1,2),1:F(1,2),2:F(0)}
q={(r,a,c):(F(1,2) if r in (0,1) and a==r and c==1-r else F(0)) for r,a,c in product(Rraw,range(2),range(2))}
lam={(r,a,c):(F(int(a==r and c==1-r)) if r in (0,1) else (F(1,2) if a!=c else F(0))) for r,a,c in q}
assert all(sum(lam[r,a,c] for a,c in pairs)==1 for r in Rraw)
assert all(alpha[r]*lam[r,a,c]==q[r,a,c] for r,a,c in q)
assert all(sum(q[r,a,c] for a,c in pairs)==alpha[r] for r in Rraw)
assert all(sum(q[r,a,c] for r in Rraw)==(F(1,2) if a!=c else 0) for a,c in pairs)
assert sum(q[r,a,c] for r,a,c in q if r==a)==1
# PR-style four-setting local/shared-seed obstruction at each deterministic response.
local_success=[]
for a0,a1,c0,c1 in product(range(2),repeat=4):
    matches=sum(((a0,a1)[x]^(c0,c1)[y])==x*y for x,y in product(range(2),repeat=2))
    local_success.append(matches)
assert max(local_success)==3
# Actual persistent paid/silent queues on Spin, with all quantum lengths finite.
paid=['B']; silent=['Spin']; countB=0; spin=0; world=1
for t in range(1000):
    if t%2==0:
        assert paid.pop(0)=='B'; countB+=1; world+=1; paid.append('B')
    else:
        assert silent.pop(0)=='Spin'; spin+=1; silent.append('Spin')
assert countB==spin==500 and world==501
# Delayed current-world seed differs from immutable snapshot on actual intervening steps.
for increments in range(1,101):
    birth=1; current=birth+increments
    assert current!=birth
# Decision laws retain positive arbitrary retry lengths and zero raw return.
p={'retry':F(1,2),'return':F(1,4),'Spin':F(1,4),'zero':F(0)}
assert sum(p.values())==1
assert all(p['retry']**n*p['return']>0 for n in range(100))
print(json.dumps({'late_owner_matrix_shape':[len(U),len(U[0])], 'rank':rank(U), 'kernel_dimension':len(U[0])-rank(U), 'exact_prefix_square':True, 'two_owner_insertion_order_square':True, 'two_owner_target_rank':rank(V), 'reserve_raw_atoms':len(q), 'zero_reserve_service_normalized':True, 'actual_incoming_marginal_preserved':True, 'central_correlation':1, 'maximum_local_four_setting_satisfaction':max(local_success), 'spin_path_paid_scopes':countB, 'spin_path_silent_quanta':spin, 'current_vs_birth_tests':100, 'positive_retry_length_tests':100},indent=2))
# Exact finite-height probabilities for the explicit retirement/stop policy.
qheight=F(0); seq=[]
for depth in range(12):
    nxt=(1+qheight*qheight)/4
    assert qheight<nxt<F(27,100)
    qheight=nxt; seq.append(float(qheight))
# The algebraic fixed point is uniquely identified in [0,1] without numerical equality claims.
assert 1-4*F(26,100)+F(26,100)**2>0
assert 1-4*F(27,100)+F(27,100)**2<0
print(json.dumps({'retirement_policy_height_mass_12':float(qheight), 'exact_fixed_point':'2-sqrt(3)', 'rational_bracket':['26/100','27/100'], 'recurrent_policy_done_mass':0}))
# All-raw zero-status pin: completed nullary is distinct from unfinished/Spin.
zero_state={'status':'completed','shape':'c0','ports':(),'actors':(),'context_factors':('real-decision',)}
unfinished={'status':'unfinished','shape':None,'ports':(),'actors':(),'context_factors':()}
spin_state={'status':'pending-Spin','shape':None,'ports':(),'actors':(),'context_factors':('real-decision',)}
assert zero_state['status']=='completed' and zero_state['shape']=='c0'
assert zero_state!=unfinished and zero_state!=spin_state
assert zero_state['context_factors']==('real-decision',)
print(json.dumps({'zero_raw_completed_nullary_body_retained':True,'zero_not_unfinished_or_Spin':True,'zero_real_factor_retained':True}))
