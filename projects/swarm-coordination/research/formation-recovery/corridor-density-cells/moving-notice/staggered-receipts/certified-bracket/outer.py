from fractions import Fraction
import json

def outer(k, saved=None):
    n=2*k
    size=10*(n+1)
    var=lambda i,j,m: (n+1)*(2*i+m)+j
    up=[];be=[];eq=[];ee=[]
    def add(L,R,pairs,r):
        t={}
        for i,v in pairs:t[i]=t.get(i,0)+v
        L.append({i:v for i,v in t.items() if v});R.append(r)
    def U(x,y):add(up,be,x,y)
    def E(x,y):add(eq,ee,x,y)
    for i in range(5):
        E([(var(i,0,0),1)],0)
        E([(var(i,0,1),1)],0)
        E([(var(i,n,1),1)],0)
    for j in range(n+1):
        for m in range(2):
            E([(var(0,j,m),1),(var(4,j,m),1)],0)
            if j<=k:E([(var(1,j,m),1),(var(3,j,m),1)],0)
        for i in range(5):
            v=var(i,j,1)
            for sg in (-1,1):U([(v,sg)],2*k)
            if i:
                q=var(i-1,j,0); r=var(i,j,0)
                U([(r,1),(q,-1)],6*k*k)
                U([(r,-1),(q,1)],0)
            if j==n:continue
            a,b=var(i,j,0),var(i,j+1,0)
            c,d=var(i,j,1),var(i,j+1,1)
            for sg in (-1,1):
                U([(d,sg),(c,-sg)],2)
                for tangent in (-2,-1,0,1,2):
                    U([(b,4*sg),(a,-4*sg),(c,-4*sg-2*tangent),(d,-4*sg+2*tangent)],
                      4+tangent*tangent)
    def sparse(rows):
        from scipy.sparse import coo_matrix
        I=[];J=[];V=[]
        for i,row in enumerate(rows):
            for j,v in row.items():I.append(i);J.append(j);V.append(v)
        return coo_matrix((V,(I,J)),shape=(len(rows),size)).tocsc()
    objective=[0]*size
    objective[var(2,n,0)]=1; objective[var(0,n,0)]=-1
    if saved is None:
        from scipy.optimize import linprog
        sol=linprog([-v for v in objective],A_ub=sparse(up),b_ub=be,
                   A_eq=sparse(eq),b_eq=ee,bounds=(None,None),method="highs")
        assert sol.success
        mu=[Fraction(-v).limit_denominator(500000) for v in sol.ineqlin.marginals]
        nu=[Fraction(-v).limit_denominator(500000) for v in sol.eqlin.marginals]
        saved={"k":k,"ineq":[[i,str(v)] for i,v in enumerate(mu) if v],
                      "eq":[[i,str(v)] for i,v in enumerate(nu) if v]}
    arr=[Fraction(0)]*size; rhs=Fraction(0)
    for kind,rows,rv in (("ineq",up,be),("eq",eq,ee)):
        indices=set()
        for j, f in saved[kind]:
            assert j not in indices and 0<=j<len(rows)
            indices.add(j)
            v=Fraction(f)
            if kind=="ineq":assert v>=0
            for i,q in rows[j].items():arr[i]+=v*q
            rhs+=v*rv[j]
    assert arr==objective
    upper=rhs/(2*k*k)
    return saved, {"k":k,"upper":str(upper),"rows":len(saved["ineq"])+len(saved["eq"])}
if __name__=="__main__":
    import sys
    from pathlib import Path
    p=Path(__file__).with_name("upper.json")
    if "--search" in sys.argv:
        p.write_text(json.dumps([outer(k)[0] for k in (4,8,16,32,64)],separators=(",",":"))+"\n")
    for r in json.loads(p.read_text()):
        print(json.dumps(outer(r["k"],r)[1],sort_keys=True))
