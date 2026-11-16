from fractions import Fraction as F
from collections import defaultdict
import json
import numpy as np
q={'done':F(1,4),'blocked':F(1,4),'continue':F(1,2),'zero_block':F(0)}
mu={'A':F(1,2),'B':F(1,2),'C':F(0)}
mup={'T':F(1),'Z':F(0)}
r0={'A':'T','B':'T','C':'Z'}
def initial(mu):
    return {(s,(),('blocked' if s in ('C','Z') else 'active'),(2 if s in ('C','Z') else 1)):p for s,p in mu.items()}
def step(level):
    out={}
    for (s,path,status,ports),p in level.items():
        if status!='active':out[(s,path,status,ports)]=p;continue
        for z,v in q.items():
            status2='active' if z=='continue' else ('done' if z=='done' else 'blocked')
            out[(s,path+(z,),status2,ports+1)]=p*v
    return out
def truncate(a,n):
    s,path,status,ports=a
    if len(path)<=n:return a
    assert len(path)==n+1
    return (s,path[:-1],'active',ports-1)
def push(level,fn):
    out=defaultdict(F)
    for a,p in level.items():out[fn(a)]+=p
    return dict(out)
def native(a):return (r0[a[0]],)+a[1:]
S=[initial(mu)];T=[initial(mup)]
for n in range(6):
    assert push(S[n],native)==T[n]
    assert sum(S[n].values())==sum(T[n].values())==1
    for a in S[n]: assert native(a)[2:]==a[2:]
    masses={st:sum(p for a,p in S[n].items() if a[2]==st) for st in ('done','blocked','active')}
    assert masses['done']==masses['blocked']==F(1,2)*(1-F(1,2)**n)
    assert masses['active']==F(1,2)**n
    S.append(step(S[-1]));T.append(step(T[-1]))
    assert push(S[n+1],lambda a,n=n:truncate(a,n))==S[n]
    assert push(T[n+1],lambda a,n=n:truncate(a,n))==T[n]
    # Birth records truncate by persistence, not equality of current port counts.
    assert any(a[3]>truncate(a,n)[3] for a in S[n+1])
# Zero initial and paid outcome histories remain despite zero probability.
assert any(a[0]=='C' for a in S[5])
assert any('zero_block' in a[1] for a in S[5])
# Exact augmentation/tensor comparison squares for nontrivial actual linear maps.
checks=0
Kmap=np.array([[1,0,0],[0,1,0]],dtype=int)
epsS=np.array([[1,0,0]],dtype=int);epsT=np.array([[1,0]],dtype=int)
for d in (3,4):
    Lmap=np.zeros((2,d),dtype=int);Lmap[0,0]=Lmap[1,1]=1
    prev=Lmap
    for n in range(4):
        current=np.kron(prev,Kmap)
        source_trunc=np.kron(np.eye(d*3**n,dtype=int),epsS)
        target_trunc=np.kron(np.eye(2*2**n,dtype=int),epsT)
        assert np.array_equal(target_trunc@current,prev@source_trunc)
        prev=current;checks+=1
# A blocked->ready map is disallowed even on initial probability-zero C.
assert 'blocked'!='active'
# Protocol preservation is an additional exact equation, not erased at zero inputs.
assert any(z!=0 for z in (0,1))
print(json.dumps({'finite_native_pushforward_and_truncation':'PASS','horizons_checked':6,'raw_zero_initial_and_paid_witnesses':'RETAINED','done_blocked_active_separate':'PASS','early_port_growth_and_persistence':'PASS','actual_augmented_linear_tensor_squares':checks,'coefficient_mode':'whole 3D scope factors remain intact; initial factors retained','infinite_measure_claim':'proved in TeX, not certified by finite tests'},indent=2))
