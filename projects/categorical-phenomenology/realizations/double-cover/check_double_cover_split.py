import numpy as np
from itertools import product
rng=np.random.default_rng(20261103)
maxerr=0.

def check(a,b):
    global maxerr
    err=float(np.max(np.abs(np.asarray(a)-np.asarray(b))))
    maxerr=max(maxerr,err)
    assert err<1e-9,(err,a,b)

def repair(Q):
    r,k=Q.shape
    eta=.37/k
    F=np.maximum(Q-eta,0);F/=F.sum(axis=1,keepdims=True)
    theta=np.minimum(Q/eta,1)
    B=theta.T+(1-theta.sum(axis=0))[:,None]/r
    return F,B

for r in range(1,8):
  for k in range(r,11):
    for trial in range(20):
      owners=np.r_[np.arange(r),rng.integers(-1,r,size=k-r)]
      rng.shuffle(owners)
      Q=np.array([rng.random(k)*(owners==a) for a in range(r)])
      Q/=Q.sum(axis=1,keepdims=True)
      F,B=repair(Q)
      check(F@B,np.eye(r));check(B.sum(axis=1),np.ones(k))
      assert F.min()>=0 and B.min()>=-1e-14
      perm=rng.permutation(r)
      Fp,Bp=repair(Q[perm])
      check(Fp,F[perm]);check(Bp,B[:,perm])
      L=np.empty((k,r))
      for i,a in enumerate(owners):
        L[i]=np.eye(r)[a] if a>=0 else rng.dirichlet(np.ones(r))
      for t in [0,.2,.5,.9,1]:
        check(((1-t)*Q+t*F)@L,np.eye(r))
        check(F@((1-t)*L+t*B),np.eye(r))

for k in range(2,11):
  for trial in range(80):
    u=rng.normal(size=k);u-=u.mean();u/=np.linalg.norm(u)
    c=1/np.sqrt(k*(k-1));assert max(u)>=c-1e-12 and min(u)<=-c+1e-12,(k,u,c)
    eta=c/2
    q1=np.maximum(u-eta,0);q1/=q1.sum()
    q2=np.maximum(-u-eta,0);q2/=q2.sum()
    Q=np.array([q1,q2]);clip=np.clip(u/eta,-1,1)
    L=np.array([(1+clip)/2,(1-clip)/2]).T
    check(Q@L,np.eye(2))
    m=3
    M=rng.dirichlet(np.ones(2*m),size=2).reshape(2,m,2).transpose(1,0,2)
    pi=rng.dirichlet(np.ones(2));rho=pi@Q
    N=np.array([L@A@Q for A in M])
    S=np.eye(k)+.08*rng.normal(size=(k,k));S-=((S.sum(axis=1)-1)/k)[:,None]
    inv=np.linalg.inv(S);rho=rho@S;N=np.array([inv@A@S for A in N])
    one=np.ones(k);two=np.ones(2)
    f=np.array([pi@A@two for A in M])
    H=np.array([[pi@A@B@two for B in M]for A in M]);C=H-np.outer(f,f)
    alpha=np.array([(pi@A-f[y]*pi)[0]for y,A in enumerate(M)])
    beta=np.array([(A@two)[0]-(A@two)[1]for A in M])
    check(C,np.outer(alpha,beta))
    d=sum(alpha[y]*(rho@A-f[y]*rho)for y,A in enumerate(N))
    check(d@one,0)
    check([d@A@one for A in N],alpha@alpha*beta)
    check(sum(N)@one,one)
    for word in product(range(m),repeat=3):
      a=pi.copy();b=rho.copy()
      for y in word:a=a@M[y];b=b@N[y]
      check(a@two,b@one)
print(f'All buffered-decoder, equivariance, homotopy, normalization, signed-extraction, and three-step transfer checks passed. Maximum residual: {maxerr:.3g}.')
