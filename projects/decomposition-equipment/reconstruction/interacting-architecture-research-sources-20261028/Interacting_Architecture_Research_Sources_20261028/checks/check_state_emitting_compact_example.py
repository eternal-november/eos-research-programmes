import itertools
import sympy as s

n=3
xs=list(itertools.product([0,1],repeat=n)); N=len(xs)
C=[(0,)]+[S for j in range(1,n) for S in [(j,),(0,j)]]
q=len(C)
chi=lambda S:s.Matrix([[(-1)**sum(x[j] for j in S) for x in xs]])
J=s.ones(N,N)/N
D=s.eye(N)/2+J/4
for k,S in enumerate(C):
    T=C[(k+1)%q]
    M=(s.ones(N,N)+chi(S).T*chi(T))/N
    assert min(M)>=0
    assert list(s.ones(1,N)*M)==[1]*N
    D += M/(4*q)
assert min(D)>0 and D.det()!=0
assert s.ones(1,N)*D==s.ones(1,N)
for k,S in enumerate(C):
    assert chi(S)*D==chi(S)/2+chi(C[(k+1)%q])/(4*q)

E=[s.diag(*[int(x[0]==y) for x in xs]) for y in (0,1)]
local=[s.Matrix([[s.Rational(3,4),s.Rational(1,4)],[s.Rational(1,4),s.Rational(3,4)]]),s.Matrix([[s.Rational(3,4),s.Rational(1,2)],[s.Rational(1,4),s.Rational(1,2)]])]
assert s.Matrix.hstack(s.eye(2).reshape(4,1),*[k.reshape(4,1) for k in local]).rank()==3
assert all(min(k)>0 and k.det()!=0 and s.ones(1,2)*k==s.ones(1,2) for k in local)
Ks=[s.eye(N)]
for j in range(n):
  for K in local:
    fs=[s.eye(2)]*n;fs[j]=K
    Ks.append(s.kronecker_product(*fs))
Hs=[e*D*k for k in Ks for e in E]
W=s.Matrix.vstack(s.ones(1,N),*[chi(S) for S in C])
assert W.rank()==2*n
assert all(s.Matrix.vstack(W,W*h).rank()==2*n for h in Hs)

# Successively close a basis, with exact rational rank tests.
def closure(vectors,apply):
    B=list(vectors)
    while True:
      old=len(B)
      for v in list(B):
        for h in Hs:
          z=apply(v,h)
          if s.Matrix.vstack(*B,z).rank()>len(B):B.append(z)
      if len(B)==old:return B
rows=closure([s.ones(1,N)],lambda v,h:v*h)
cols=closure([s.ones(1,N)/N],lambda v,h:(h*v.T).T)
assert len(rows)==2*n
assert len(cols)==N
print({'n':n,'hidden_dimension':N,'predictive_rank':len(rows),'reachable_dimension':len(cols),'minimum_D_entry':min(D),'determinant_D':D.det(),'all_states_separated':len(set(tuple(W[:,j]) for j in range(N)))==N})
