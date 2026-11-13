from pathlib import Path
"""Finite numeric regression checks. These do not prove bundle obstructions."""
import json, itertools
import numpy as np
from scipy.linalg import null_space
rng=np.random.default_rng(20261103)
maxerr={}
def chk(name,a,b=0,tol=2e-11):
    e=float(np.max(np.abs(np.asarray(a)-np.asarray(b))))
    maxerr[name]=max(maxerr.get(name,0),e)
    if e>tol: raise AssertionError((name,e))
def stochastic(name,A):
    if float(np.min(A)) < -2e-13: raise AssertionError((name,'negative',float(np.min(A))))
    chk(name+'_rows',A.sum(axis=1),1)
def basis(m): return null_space(np.ones((1,m)))
def Hmake(u,A,beta):
    m=len(u); return np.vstack([np.ones(m)/m, np.ones((m-1,m))/m+beta*np.outer(A.T@u,u)])
def dynamic(u,alpha,delta):
    m=len(u); c=np.ones(m)/m
    eta=1/(2*np.sqrt(m*(m-1)))
    h=np.clip(u/eta,-1,1)
    L=np.column_stack([(1+h)/2,(1-h)/2])
    pp=np.maximum(u-eta,0); pm=np.maximum(-u-eta,0)
    assert pp.sum()>0 and pm.sum()>0
    Q=np.vstack([pp/pp.sum(),pm/pm.sum()])
    S=np.array([[0.,1.],[1.,0.]])
    J=np.ones((2,2))/2
    M={}; X={}
    for act,R in [('hold',np.eye(2)),('flip',S),('refresh',J)]:
        M[act]=[R@np.diag([c[y]+delta*u[y],c[y]-delta*u[y]]) for y in range(m)]
        X[act]=[L@B@Q for B in M[act]]
    return L,Q,M,X
samples=0
for d in range(0,7):
    m=d+2; A=basis(m); alpha=.4; delta=1/(3*m); beta=alpha*delta
    for rep in range(15):
        v=rng.normal(size=m-1); v/=np.linalg.norm(v); u=A@v
        H=Hmake(u,A,beta)
        stochastic('H',H)
        chk('H_antipodal',H,Hmake(-u,A,beta))
        assert np.linalg.matrix_rank(H,tol=1e-11)==2
        pi=np.vstack([np.array([.5,.5]),np.column_stack([(1+alpha*v)/2,(1-alpha*v)/2])])
        e=np.vstack([np.ones(m)/m+delta*u,np.ones(m)/m-delta*u])
        chk('H_local_factor',H,pi@e)
        L,Q,M,X=dynamic(u,alpha,delta)
        Ln,Qn,Mn,Xn=dynamic(-u,alpha,delta)
        stochastic('L',L); stochastic('Q',Q); chk('QL',Q@L,np.eye(2))
        S=np.array([[0.,1.],[1.,0.]])
        chk('L_antipodal',Ln,L@S);chk('Q_antipodal',Qn,S@Q)
        rho=pi@Q; stochastic('rho',rho);chk('preparation_link',rho@L,pi)
        for act in M:
            stochastic('transition_'+act,sum(X[act]))
            for y in range(m):
                chk('statewise_'+act,X[act][y]@L,L@M[act][y])
                chk('global_antipodal_'+act,Xn[act][y],X[act][y])
        for repword in range(10):
            acts=rng.choice(['hold','flip','refresh'],size=6)
            ys=rng.integers(0,m,size=6)
            B=np.eye(2); C=np.eye(m)
            for act,y in zip(acts,ys): B=B@M[act][y]; C=C@X[act][y]
            chk('six_step_word_law',pi@B@np.ones(2),rho@C@np.ones(m))
        c=np.ones(m)/m
        for act,scale in [('hold',1),('flip',-1),('refresh',0)]:
            joint=np.array([[pi[0]@M['hold'][y]@M[act][z]@np.ones(2) for z in range(m)] for y in range(m)])
            chk('covariance_'+act,joint-np.outer(c,c),scale*delta**2*np.outer(u,u))
        samples+=1
# Tangent sphere: real three-state factor, positive four-state factor.
m=4;A=basis(m); beta=.02;delta=.2;c=np.ones(m)/m;e0=np.ones(m)/2
# regular unit simplex in R^3
Z=np.sqrt(m/(m-1))*A.T
for rep in range(100):
    x=rng.normal(size=3);x/=np.linalg.norm(x);P=np.eye(3)-np.outer(x,x)
    H=np.vstack([c,c+beta*P@A.T])
    F=np.outer(e0,x)+A@P
    chk('sphere_real_frame',F.T@F,np.eye(3))
    chk('sphere_real_factor',H,(H@F)@F.T)
    V=c+delta*(A@P@Z).T
    T=(beta/delta)*P
    U=np.vstack([np.ones(4)/4,(1+3*T@Z)/4])
    stochastic('sphere_positive_U',U);stochastic('sphere_positive_V',V)
    assert U.min()>0 and V.min()>0
    chk('sphere_positive_factor',H,U@V)
    assert np.linalg.matrix_rank(H,tol=1e-11)==3
# Circle seam and exact local exchange.
A=basis(3);beta=.02;delta=.1
u0=A[:,0];up=A@np.array([np.cos(np.pi),np.sin(np.pi)])
chk('circle_observation_seam',Hmake(u0,A,beta),Hmake(up,A,beta))
e0=np.vstack([np.ones(3)/3+delta*u0,np.ones(3)/3-delta*u0])
ep=np.vstack([np.ones(3)/3+delta*up,np.ones(3)/3-delta*up])
chk('circle_local_state_swap',ep,e0[::-1])
result={'status':'passed','scope':'finite numerical regression; no topological proof or novelty certification','projective_samples':samples,'sphere_samples':100,'max_errors':maxerr}
print(json.dumps(result,indent=2))
open(str(Path(__file__).resolve().with_name('topological_native_checks_results.json')),'w').write(json.dumps(result,indent=2)+'\n')
