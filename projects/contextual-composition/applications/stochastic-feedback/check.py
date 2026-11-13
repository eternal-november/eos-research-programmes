"""Exact-rational diagnostics, not a substitute for the written proofs."""
import json, random
from pathlib import Path
from sympy import Matrix, Rational as F, eye, zeros, ones

def summary(A,B,C,Q,gx,g):
    N=(eye(Q.rows)-Q).inv()
    return A+B*N*C,gx+B*N*g

def nested(A,B,C,Q,gx,g,U,V):
    NV=(eye(len(V))-Q.extract(V,V)).inv()
    BV=B[:,V]; BU=B[:,U]; CV=C[V,:]; CU=C[U,:]
    UV=Q.extract(U,V); VU=Q.extract(V,U)
    return summary(A+BV*NV*CV,BU+BV*NV*VU,CU+UV*NV*CV,
                   Q.extract(U,U)+UV*NV*VU,gx+BV*NV*g[V,:],g[U,:]+UV*NV*g[V,:])

A=zeros(1,2); B=Matrix([[F(1,2),F(1,2)]])
Q=Matrix([[F(1,4),F(1,2)],[F(1,3),F(1,3)]])
C=Matrix([[F(1,4),0],[0,F(1,3)]])
gx=Matrix([2]); g=Matrix([3,5])
T,E=summary(A,B,C,Q,gx,g)
assert T*ones(2,1)==ones(1,1)
assert nested(A,B,C,Q,gx,g,[0],[1])==(T,E)
assert nested(A,B,C,Q,gx,g,[1],[0])==(T,E)
for k in range(15):
    Tk=A+sum((B*Q**n*C for n in range(k)),zeros(1,2))
    assert (T-Tk)*ones(2,1)==B*Q**k*ones(2,1)
    assert min(T-Tk)>=0
rng=random.Random(20261113)
for trial in range(100):
    # Strict positive exit mass per internal row, hence transience.
    rows=[]
    for i in range(3):
        r=[rng.randrange(5) for _ in range(3)]+[rng.randrange(1,5),rng.randrange(1,5)]
        rows.append([F(v,sum(r)) for v in r])
    q=Matrix([r[:3] for r in rows]); c=Matrix([r[3:] for r in rows])
    b=Matrix([[F(1,3)]*3]); a=zeros(1,2)
    gg=Matrix([rng.randrange(1,9) for _ in range(3)])
    direct=summary(a,b,c,q,gx,gg)
    for j in range(3):
        assert nested(a,b,c,q,gx,gg,[k for k in range(3) if k!=j],[j])==direct
    assert direct[0]*ones(2,1)==ones(1,1)
# Inaccessible trap makes full inverse singular, but no effect on entry.
q=Matrix([[F(1,2),0],[0,1]]); b=Matrix([[1,0]]); c=Matrix([[F(1,2)],[0]])
assert (eye(2)-q).det()==0
assert summary(zeros(1,1),b[:,[0]],c[[0],:],q.extract([0],[0]),Matrix([0]),Matrix([1]))==(Matrix([1]),Matrix([2]))
# Normalize rows, then mix, differs from mix, then normalize.
p=Matrix([[1,0],[0,F(1,2)]]); mix=Matrix([[F(1,2),F(1,2)]])
def normalize(m): return Matrix([[v/sum(m.row(i)) for v in m.row(i)] for i in range(m.rows)])
assert normalize(p)==eye(2)
assert normalize(mix*p)==Matrix([[F(2,3),F(1,3)]])
assert normalize(mix*p)!=mix*normalize(p)
for denominator in [1,2,10,100,1000]:
    p=F(1,denominator)
    # Entry performs first attempt: cost1, direct exit p, loop probability1-p.
    t,e=summary(Matrix([p]),Matrix([1-p]),Matrix([p]),Matrix([1-p]),Matrix([1]),Matrix([1]))
    assert t==Matrix([1]) and e==Matrix([denominator])
result={'status':'passed','arithmetic':'SymPy exact rational','seed':20261113,
        'fixture_exit':[str(v) for v in T], 'fixture_cost':str(E[0]),
        'random_models':100,'nested_partitions_checked':302,'tail_identities':15,
        'inaccessible_trap':'passed','normalization_obstruction':'passed','retry_cost_cases':5}
Path(__file__).with_name('results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
