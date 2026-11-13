import numpy as np

def shift(n):
    D=2**n; S=np.zeros((D,D))
    for x in range(D):
        bits=[(x>>j)&1 for j in range(n)]
        y=sum(bits[j]<<( (j+1)%n) for j in range(n))
        S[y,x]=1
    return S

def z(x,j):return 1-2*((x>>j)&1)
for n in [3,5,7]:
    D=2**n; S=shift(n); A=np.eye(D)+2*S; B=A.T; U=np.linalg.solve(B,A)
    j=0;l=n//2
    # vec U has reference index x and output index y. S sends input j to output j+1.
    probs=abs(U)**2/D
    e=np.array([[z(x,j)*z(y,(j+1)%n) for x in range(D)] for y in range(D)])
    f=np.array([[z(x,l)*z(y,(l+1)%n) for x in range(D)] for y in range(D)])
    E=(probs*e).sum();F=(probs*f).sum();EF=(probs*e*f).sum()
    u1=(2**(n-1)+2)/(2**n+1); p=u1*u1
    print({'N':n,'unitarity_error':float(np.linalg.norm(U.T@U-np.eye(D))), 'semantics_error':float(np.linalg.norm(A@A.T-B@B.T)), 'E':float(E),'EF':float(EF),'expected_p':p,'covariance':float(EF-E*F),'expected_covariance':p*(1-p),'singular_min_B':float(np.linalg.svd(B,compute_uv=False)[-1])})
    assert np.allclose([E,F,EF],[p,p,p])
    assert EF-E*F>=3/16-1e-12
print('PASS: numerical regression checks for N=3,5,7; analytic proof required for unrestricted N.')
