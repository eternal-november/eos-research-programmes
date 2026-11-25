"""Check exact cell samples, assignment duals and Hall obstructions."""
from fractions import Fraction as F
from itertools import product
import json

def verify(D):
    n,m=D['n'],D['m'];A={(i,j):(F(u),F(v)) for i,j,u,v in D['edges']}
    e=sorted(set(y for z in A.values() for y in z))
    X=set(e+[F(u+v,2) for u,v in zip(e,e[1:])]) if e else {F(0)}
    C=D['claims']; assert len(C)==len(X)*(D['k']-D['h']+1)
    assert {(F(q['x']),q['k']) for q in C}==set(product(X,range(D['h'],D['k']+1)))
    lo=[];hi=[]; base=sum(D['a'])+sum(D['b'])
    for q in C:
        x,k=F(q['x']),q['k'];z=n+m-k
        G={}
        for i,j in product(range(z),repeat=2):
            if i<n and j<m:
                if (i,j) in A and A[i,j][0]<=x<=A[i,j][1]:
                    G[i,j]=D['w'][i][j]-D['a'][i]-D['b'][j]
            elif i<n or j<m:G[i,j]=0
        if 'hall' in q:
            U=set(q['hall']);assert U<=set(range(z))
            V={j for i,j in G if i in U}
            assert len(V)<len(U)
            continue
        data=q['bounds'];assert len(data)==2
        lim=[]
        for s,(M,(u,v)) in zip((1,-1),data):
            assert len(u)==len(v)==len(M)==z
            assert set(i for i,j in M)==set(j for i,j in M)==set(range(z))
            can=[s*G[i,j] for i,j in M] # reject any missing edge
            assert all(u[i]+v[j]<=s*o for (i,j),o in G.items())
            assert sum(u)+sum(v)==sum(can)
            lim.append(base+s*sum(can))
        lo.append(lim[0]);hi.append(lim[1])
    return (min(lo),max(hi)) if lo else None

if __name__=='__main__':
    with open('cert.json') as f:data=json.load(f)
    assert [verify(D) for D in data]==[(0,0),(0,1)]
    print(sum(len(D['claims']) for D in data),'clock-cell and cardinality proof obligations checked with integer dual/Hall witnesses')
