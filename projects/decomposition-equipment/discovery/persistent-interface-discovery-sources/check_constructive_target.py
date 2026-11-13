import itertools, json
import numpy as np
from pathlib import Path
rho=3/5; tau=5/7
out=[]
for k in range(2,5):
    states=np.array(list(itertools.product([0,1],repeat=k)),dtype=int)
    obs=np.array(list(itertools.product([0,1],repeat=2*k)),dtype=int)
    r=len(states)
    E=np.ones((len(obs),r))
    for i in range(k):
        E*= (1+rho*rho*(-1.)**(obs[:,2*i,None]+obs[:,2*i+1,None]+states[None,:,i]))/4
    f=states.copy(); f[:,1:]^=states[:,:-1]
    K=np.ones((r,r))
    for i in range(k): K*= (1+tau*(-1.)**(states[:,i,None]+f[None,:,i]))/2
    P=E@K.T@E.T/r
    assert np.max(abs(P.sum(axis=1)-1/len(obs)))<1e-12
    sets=[s for n in (2,4) for s in itertools.combinations(range(2*k),n)]
    pairs=list(itertools.combinations(range(2*k),2))
    X=np.array([(-1.)**obs[:,s].sum(axis=1) for s in sets])
    Y=np.array([(-1.)**obs[:,s].sum(axis=1) for s in pairs])
    moments=X@P@Y.T
    expected=np.zeros_like(moments)
    for i in range(k):
        pair=(2*i,2*i+1)
        prev=pair if i==0 else (2*i-2,2*i-1,2*i,2*i+1)
        expected[sets.index(prev),pairs.index(pair)]=rho**(4 if i==0 else 6)*tau
    assert np.max(abs(moments-expected))<1e-12
    rank=np.linalg.matrix_rank(P,tol=1e-11)
    assert rank==r
    a=moments[sets.index((0,1)),pairs.index((0,1))]
    b=moments[sets.index((0,1,2,3)),pairs.index((2,3))]
    assert abs((b/a)**.5-rho)<1e-12
    assert abs(a**3/b**2-tau)<1e-12
    # Crossing stream alone has temporally independent uniform outputs.
    stream=[sum(int(obs[j,2*i])<<i for i in range(k)) for j in range(len(obs))]
    R=np.zeros((r,len(obs))); R[stream,np.arange(len(obs))]=1
    marginal=R@P@R.T
    assert np.max(abs(marginal-1/r**2))<1e-12
    out.append(dict(k=k, moments=int(moments.size), global_rank=int(rank), max_moment_error=float(np.max(abs(moments-expected))), passed=True))
path=Path(__file__).with_name('Constructive_Target_QA.json'); path.write_text(json.dumps(out,indent=2)+'\n')
print(path.read_text())
# Exact rational rank and matrix normalization at k=2.
import sympy as sp
k=2; states=list(itertools.product([0,1],repeat=k)); obs=list(itertools.product([0,1],repeat=2*k))
rhoq=sp.Rational(3,5); tauq=sp.Rational(5,7)
Eq=sp.Matrix([[sp.prod((1+rhoq**2*(-1)**(o[2*i]+o[2*i+1]+c[i]))/4 for i in range(k)) for c in states] for o in obs])
Kq=sp.Matrix([[sp.prod((1+tauq*(-1)**(cp[i]+c[i]+(c[i-1] if i else 0)))/2 for i in range(k)) for c in states] for cp in states])
Pq=Eq*Kq.T*Eq.T/4
assert Pq.rank()==4
assert all(sum(Pq.row(i))==sp.Rational(1,16) for i in range(16))
print('Exact rational k=2 rank and uniformity checks passed.')
