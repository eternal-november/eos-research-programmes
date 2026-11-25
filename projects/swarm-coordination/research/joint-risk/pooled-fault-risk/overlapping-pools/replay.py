"""Exact certificates for robust planning from overlapping pooled diagnostics."""
from fractions import Fraction as Q
from itertools import combinations,product
from random import Random
import json,sys
from scipy.optimize import linprog

def dot(a,b):return sum(x*y for x,y in zip(a,b))
def transpose(H,n):return [tuple(row[i] for row in H) for i in range(n)]
def bounded_feasibility(H,z,l,u,w):
    return all(a<=x<=b for a,x,b in zip(l,w,u)) and [dot(r,w) for r in H]==z
def yvertices(H,z,l,u):
    m=len(u);r=len(H)
    for b in combinations(range(m),r):
        fixed=[i for i in range(m) if i not in b]
        for x in product(*[[l[i],u[i]] for i in fixed]):
            mat=[[Q(row[j]) for j in b]+[rhs-dot([row[j] for j in fixed],x)]
                 for row,rhs in zip(H,z)]
            for i in range(r):
                piv=next((j for j in range(i,r) if mat[j][i]),None)
                if piv is None:break
                mat[piv],mat[i]=mat[i],mat[piv];den=mat[i][i];mat[i]=[v/den for v in mat[i]]
                for j in range(r):
                    if j!=i:mat[j]=[a-mat[j][i]*c for a,c in zip(mat[j],mat[i])]
            else:
                y=[0]*m
                for i,v in zip(fixed,x):y[i]=v
                for i,v in zip(b,mat):y[i]=v[-1]
                if bounded_feasibility(H,z,l,u,y):yield tuple(y)

def exact(H,z,l,u,p,alpha,witness,export=None):
    """Result accepted only with matching exact rational primal and dual certificates."""
    m=len(p);r=len(H);columns=transpose(H,m)
    assert bounded_feasibility(H,z,l,u,witness)
    rem=[v-dot(h,l) for h,v in zip(H,z)];c=[h-q for h,q in zip(u,l)]
    rows=[]
    for i in range(m):
        row=[0]*(2*m+r)
        row[i]=1;row[m+i]=-1;row[2*m:]=[-v for v in columns[i]];rows.append(row)
    rows.append(list(l)+c+rem)
    approx=linprog([-x for x in p]+[0]*(m+r),A_ub=rows,b_ub=[0]*m+[alpha],
                   bounds=[(0,1)]*m+[(0,None)]*m+[(None,None)]*r,method='highs')
    if not approx.success:raise RuntimeError(approx.message)
    fr=lambda v:Q(float(v)).limit_denominator(10**7)
    nums=list(map(fr,approx.x));lam=nums[:m];slack=nums[m:2*m];eta=nums[2*m:]
    dual=[fr(-v) for v in approx.ineqlin.marginals];q=dual[:m];beta=dual[-1]
    # No solver tolerance is used in these certificate checks.
    assert all(0<=v<=1 for v in lam)
    assert all(a>=0 and b<=a+dot(col,eta) for a,b,col in zip(slack,lam,columns))
    assert dot(l,lam)+dot(c,slack)+dot(rem,eta)<=alpha
    assert beta>=0 and all(0<=v<=beta*w for v,w in zip(q,c))
    assert all(dot(row,q)==beta*v for row,v in zip(H,rem))
    upper=beta*alpha+sum(max(0,a-b-beta*v) for a,b,v in zip(p,q,l))
    assert upper==dot(p,lam),(upper,dot(p,lam),m)
    if export is not None:
        v=lambda a:list(map(str,a))
        export.append(dict(H=H,z=v(z),lower=v(l),upper=v(u),weights=v(p),
            cap=str(alpha),witness=v(witness),policy=v(lam),slack=v(slack),
            eta=v(eta),dual=v(q),beta=str(beta),utility=str(upper)))
    return upper,lam

def one_example():
    l=[Q(0)]*3;u=[Q(1,4)]*3;H=[[1,1,0],[0,1,1]];z=[Q(1,4)]*2
    vs=list(yvertices(H,z,l,u))
    yes=(Q(1,2),Q(1),Q(1,2));no=(1,0,0)
    assert set(dot(yes,y) for y in vs)=={Q(1,4)}
    assert set(dot(no,y) for y in vs)=={0,Q(1,4)}
    return 'nonconstant policy is identified by the two overlapping pools'

def verify(export=None):
    rng=Random(420)
    n=0;verts=0;witnesses=[]
    for m in range(2,8):
        for i in range(18):
            H=[[1]*m]
            if m>=3 and i%3!=0:H.append([int(k%2==0) for k in range(m)])
            if m>=4 and i%3==2:H.append([int(k%3==0) for k in range(m)])
            p=[Q(1,m)]*m
            l=[Q(rng.randrange(4),40*m) for _ in range(m)]
            u=[v+Q(rng.randrange(12),40*m) for v in l]
            w=[a+Q(rng.randrange(5),4)*(b-a) for a,b in zip(l,u)]
            z=[dot(r,w) for r in H]
            alpha=Q(rng.randrange(6),40)
            value,lam=exact(H,z,l,u,p,alpha,w)
            ys=sorted(set(yvertices(H,z,l,u)))
            assert ys and max(dot(y,lam) for y in ys)<=alpha
            brute=linprog([-k for k in p],A_ub=ys,b_ub=[alpha]*len(ys),bounds=(0,1),method='highs')
            assert brute.success and abs(float(value)+brute.fun)<1e-8
            n+=1;verts+=len(ys)
    for m in (32,64,128,256):
        p=[Q(1,m)]*m
        l=[Q(k%3,20*m) for k in range(m)]
        u=[v+Q(1+k%5,20*m) for k,v in enumerate(l)]
        w=[(a+b)/2 for a,b in zip(l,u)]
        H=[[1]*m,[int(k%2==0) for k in range(m)],[int(k%3==0) for k in range(m)]]
        z=[dot(r,w) for r in H]
        value,lam=exact(H,z,l,u,p,Q(1,10),w,export)
        witnesses.append(dict(contexts=m,pools=3,retention=str(value),npositive=sum(x>0 for x in lam)))
    return dict(small_cases=n,explicit_vertices=verts,large_exact_certificates=witnesses,example=one_example())
if __name__=='__main__':
    export=[] if len(sys.argv)>2 else None
    ans=json.dumps(verify(export),sort_keys=True,indent=2)+'\n'
    if export is not None:open(sys.argv[2],'w').write(json.dumps(export,separators=(',',':'),sort_keys=True)+'\n')
    if len(sys.argv)>1:open(sys.argv[1],'w').write(ans)
    else:print(ans,end='')
