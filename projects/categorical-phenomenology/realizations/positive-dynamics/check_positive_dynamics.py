import itertools, math
import numpy as np

q=.25
ell=np.array([1.,.5,0.])
b=np.array([2/3,2/3,0.])
S=np.array([[2/3,2.,1.],[2/3,-2.,0.],[0.,0.,1.]])
Si=np.linalg.inv(S)
maxerr=0.
checks=0
minsing=1.
def check(err,tol=1e-11):
    global maxerr,checks
    err=float(np.max(np.abs(err)))
    maxerr=max(maxerr,err); checks+=1
    assert err<tol, (err,tol)
def mats(r,th):
    R=np.array([[math.cos(th),-math.sin(th)],[math.sin(th),math.cos(th)]])
    A0=np.zeros((3,3)); A0[0,0]=q; A0[1:,1:]=q*r*R
    d=ell@(np.eye(3)-A0)
    return A0,np.outer(b,d)
def surv(n,r,th): return q**n*(2+r**n*math.cos(n*th))/3

def rw(word,r,th):
    value=1.; age=0
    for a in word:
        if a: value*=surv(age,r,th)-surv(age+1,r,th); age=0
        else: age+=1
    return value*surv(age,r,th)

for x in np.linspace(0,.25,31):
    r=1-x*x; th=math.pi/2+x
    A=mats(r,th); N=[(Si@a@S).T for a in A]
    check((N[0]+N[1])@np.ones(3)-np.ones(3))
    H=np.array([[surv(i+j,r,th) for j in range(3)] for i in range(3)])
    minsing=min(minsing,np.linalg.svd(H,compute_uv=False)[-1])
    assert np.linalg.det(H)!=0
    bs=np.linalg.solve(np.eye(3)-A[0],b); bs/=ell@bs
    check(sum(A)@bs-bs)
    alpha_star=Si@bs
    check(alpha_star.sum()-1)
    check(alpha_star@(N[0]+N[1])-alpha_star)
    for n in range(8):
        total=0.
        for word in itertools.product((0,1),repeat=n):
            z=b.copy(); row=np.array([1.,0.,0.])
            for a in word: z=A[a]@z; row=row@N[a]
            p=ell@z
            check(p-rw(word,r,th)); check(p-row@np.ones(3))
            assert p>0
            total+=p
        check(total-1)

for m in (1,2,3,4,5,7,11,16,32):
    th=2*math.pi/m; A=mats(1,th)
    N0=np.zeros((m,m)); N1=np.zeros((m,m))
    for j in range(m):
        g=q*(2+math.cos((j+1)*th))/(2+math.cos(j*th))
        N0[j,(j+1)%m]=g; N1[j,0]=1-g
    pi=np.array([surv(j,1,th) for j in range(m)]); pi/=sum(pi)
    check(pi@(N0+N1)-pi)
    bs=np.linalg.solve(np.eye(3)-A[0],b); bs/=ell@bs
    for n in range(7):
        for word in itertools.product((0,1),repeat=n):
            row=np.eye(m)[0]; st=pi.copy(); z=bs.copy()
            for a in word:
                row=row@(N0,N1)[a]; st=st@(N0,N1)[a]; z=A[a]@z
            check(row.sum()-rw(word,1,th)); check(st.sum()-ell@z)

# Explicit continuous cone-generator normalization for chosen damped points.
def weights(v,U):
    m=len(U); phi=math.atan2(v[1],v[0])%(2*math.pi)
    j=min(m-1,int(phi*m/(2*math.pi))); j1=(j+1)%m
    ab=np.linalg.solve(np.stack((U[j],U[j1]),axis=1),v)
    w=np.full(m,(1-ab.sum())/m); w[j]+=ab[0]; w[j1]+=ab[1]
    assert min(w)>-1e-12
    check(w@U-v); check(w.sum()-1)
    return w
for x in (.25,.1,.05,.02,.01):
    r=1-x*x; th=math.pi/2+x
    m=max(6,math.ceil(math.pi/math.acos(r)))
    R=1/math.cos(math.pi/m)
    U=np.array([[R*math.cos(2*math.pi*j/m),R*math.sin(2*math.pi*j/m)] for j in range(m)])
    Graw=np.column_stack((np.ones(m),U)).T
    a=ell@Graw; G=Graw/a
    beta=(2/3)*weights(np.array([1.,0.]),U)*a
    A0,A1=mats(r,th); d=ell@(np.eye(3)-A0)
    B0=np.empty((m,m))
    for j in range(m):
        out=A0@Graw[:,j]/q
        B0[:,j]=(q/a[j])*weights(out[1:],U)*a
    B1=np.outer(beta,d@G)
    check(G@beta-b); check(G@B0-A0@G); check(G@B1-A1@G)
    check((B0+B1).sum(axis=0)-1)
    assert min(B0.ravel())>-1e-12 and min(B1.ravel())>0
    ratio=(1-r**4*math.cos(4*x))/(r**4*math.sin(4*x))
    lower=math.pi/math.atan(ratio)
    assert lower<=m
    print(f'x={x:g}: lower={lower:.6f}, polygon upper={m}, x*lower={x*lower:.6f}')
# A finite zero-age truncation matches every word through its chosen horizon.
for r,th in ((1.,math.sqrt(2)),(.98,math.pi/2+.1)):
    for L in range(1,8):
        N0=np.zeros((L+1,L+1)); N1=np.zeros((L+1,L+1))
        for j in range(L):
            g=surv(j+1,r,th)/surv(j,r,th)
            N0[j,j+1]=g; N1[j,0]=1-g
        N0[L,L]=q; N1[L,0]=1-q
        check((N0+N1).sum(axis=1)-1)
        for n in range(L+1):
            for word in itertools.product((0,1),repeat=n):
                row=np.eye(L+1)[0]
                for a in word: row=row@(N0,N1)[a]
                check(row.sum()-rw(word,r,th))
print(f'checks={checks}, max residual={maxerr:.3g}, minimum sampled Hankel singular value={minsing:.6g}')
