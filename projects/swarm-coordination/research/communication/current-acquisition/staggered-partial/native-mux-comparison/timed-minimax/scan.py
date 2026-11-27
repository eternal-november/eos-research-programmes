from fractions import Fraction as F
from itertools import permutations, product
from mux import M
G=(1,1,-1,-1)
TIMES=(F(0),F(1),F(2))

def recovery(rows,target=G):
    n=len(rows)
    a=[[F(row[j]) for row in rows]+[F(target[j])] for j in range(4)]
    for j in range(n):
        k=next((i for i in range(j,4) if a[i][j]),None)
        if k is None:return None
        a[j],a[k]=a[k],a[j]
        b=a[j][j]
        a[j]=[x/b for x in a[j]]
        for i in range(4):
            if i!=j:
                b=a[i][j]
                a[i]=[x-b*y for x,y in zip(a[i],a[j])]
    if any(a[k][-1] for k in range(n,4)):return None
    return tuple(a[i][-1] for i in range(n))

def choices():
    for js in permutations(range(len(M)),3):
        rows=tuple(M[j] for j in js)
        a=recovery(rows)
        if a is not None:
            assert all(a)
            yield js,rows,a

PLANS=tuple(choices())

def radius(rows,a,rates,B,D,noise,T,times=TIMES):
    raw=F(0)
    span=times+(T,)
    for i,r in enumerate(rates):
        z=F(0)
        for j in range(len(a)):
            z+=a[j]*rows[j][i]
            raw+=r*abs(z)*(span[j+1]-span[j])
        assert z==G[i]
    bias=[(j,a[j]*sum(row)) for j,row in enumerate(rows) if sum(row)]
    assert sum(x for j,x in bias)==0
    assert len(bias) in (0,2)
    maybe=0
    if bias:
        (j,x),(k,_)=bias
        maybe=abs(x)*min(2*B,D*(times[k]-times[j]))
    e=sum(abs(x)*y for x,y in zip(a,noise))
    return raw,maybe,e

def opt(rates,B,D,noise,T,force=None):
    scores=[]
    for js,Q,a in PLANS:
        if force=='only-diff' and max(js)>=4:continue
        if force=='mixed' and max(js)<4:continue
        v=radius(Q,a,rates,B,D,noise,T)
        scores.append((sum(v),js,v,a))
    return min(scores)

def witness():
    for L in product((0,1,2,5,10),repeat=4):
        weak=opt(L,F(200),F(0),(0,0,0),F(2))
        shield=opt(L,F(200),F(10),(0,0,0),F(2))
        mixed=opt(L,F(200),F(10),(0,0,0),F(2),'mixed')
        diff=opt(L,F(200),F(0),(0,0,0),F(2),'only-diff')
        if weak[0]<diff[0] and shield[0]<mixed[0]:
            return L,weak,shield,mixed,diff

if __name__=='__main__':
    print(len(PLANS),witness())
