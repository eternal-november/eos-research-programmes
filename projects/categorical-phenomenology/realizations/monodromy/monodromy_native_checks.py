import numpy as np, itertools, json
from pathlib import Path
root=Path(__file__).resolve().parent
pi=np.ones(3)/3
c=pi.copy()
a=np.array([1.,-1.,0.])/np.sqrt(2)
b=np.array([1.,1.,-2.])/np.sqrt(6)
P=np.eye(3)[[1,2,0]]
J=np.ones((3,3))/3
delta=0.2

def emission(t):
    ang=2*np.pi*t/3+2*np.pi*np.arange(3)/3
    return c+delta*(np.cos(ang)[:,None]*a+np.sin(ang)[:,None]*b)

def ql(t):
    Q=np.eye(4)[:3].copy(); L=np.vstack([np.eye(3),pi])
    stages=[('L',3,pi,np.eye(3)[0]),
            ('Q',0,np.eye(4)[0],np.eye(4)[3]),
            ('L',0,np.eye(3)[0],np.eye(3)[2]),
            ('Q',2,np.eye(4)[2],np.eye(4)[0]),
            ('L',2,np.eye(3)[2],np.eye(3)[1]),
            ('Q',1,np.eye(4)[1],np.eye(4)[2]),
            ('L',1,np.eye(3)[1],np.eye(3)[0]),
            ('Q',0,np.eye(4)[3],np.eye(4)[1]),
            ('L',3,np.eye(3)[0],pi)]
    for i,(typ,row,start,end) in enumerate(stages):
        if 9*t<i: break
        u=np.clip(9*t-i,0,1)
        # Polynomial smoothstep for regression; C-infinity flat replacement
        # in the proof has exactly the same support and algebraic identities.
        u=u*u*(3-2*u)
        (L if typ=='L' else Q)[row]=(1-u)*start+u*end
    return Q,L

errs={}
def check(name,value): errs[name]=max(errs.get(name,0),float(np.max(np.abs(value))))
V0=emission(0); H0=V0.T@V0/3
rng=np.random.default_rng(20261103)
ts=np.unique(np.r_[np.linspace(0,1,181),np.arange(10)/9,rng.random(100)])
minimum_emission=1.; minimum_signed=1.
for t in ts:
    V=emission(t); Q,L=ql(t); rho=pi@Q
    S=V@np.linalg.inv(V0)
    E=L@V
    minimum_emission=min(minimum_emission,E.min())
    check('QL',Q@L-np.eye(3)); check('Q_rows',Q.sum(1)-1);check('L_rows',L.sum(1)-1)
    check('constant_hankel',V.T@V/3-H0)
    check('signed_S_orthogonal',S@S.T-np.eye(3)); check('signed_S_terminal',S@np.ones(3)-1)
    local={}; native={}; signed={}
    for name,Ta in [('hold',np.eye(3)),('cycle',P),('refresh',J)]:
        T=L@Ta@Q
        for y in range(3):
            M=Ta@np.diag(V[:,y]); X=L@M@Q; N=np.linalg.solve(S,M@S)
            local[name,y]=M; native[name,y]=X; signed[name,y]=N
            minimum_signed=min(minimum_signed,N.min())
            check('statewise_'+name,X@L-L@M)
            check('state_emitting_'+name,T@np.diag(E[:,y])-X)
        check('native_transition_'+name,T.sum(1)-1)
    for _ in range(12):
        actions=rng.choice(['hold','cycle','refresh'],7)
        outcomes=rng.integers(3,size=7)
        r1=pi.copy();r2=rho.copy();r3=pi.copy()
        for act,y in zip(actions,outcomes):
            r1=r1@local[act,y];r2=r2@native[act,y];r3=r3@signed[act,y]
        check('seven_step_positive',r2.sum()-r1.sum())
        check('seven_step_signed',r3.sum()-r1.sum())
Q0,L0=ql(0);Q1,L1=ql(1)
check('Q_monodromy',Q1-P@Q0);check('L_monodromy',L1-L0@P.T)
for y in range(3):
    check('native_seam',L1@np.diag(emission(1)[:,y])@Q1-L0@np.diag(V0[:,y])@Q0)
    S1=emission(1)@np.linalg.inv(V0)
    check('signed_seam',np.linalg.solve(S1,np.diag(emission(1)[:,y])@S1)-np.diag(V0[:,y]))
result={'status':'passed' if max(errs.values())<1e-12 else 'failed', 'parameter_samples':len(ts),'minimum_emission_entry':float(minimum_emission),'minimum_signed_kernel_entry':float(minimum_signed),'hankel_eigenvalues':np.linalg.eigvalsh(H0).tolist(),'max_errors':errs,'scope':'numeric formula regression, not a monodromy proof or novelty certification'}
(root/'monodromy_native_checks_results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
assert result['status']=='passed'
