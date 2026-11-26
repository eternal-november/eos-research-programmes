"""Exact robust residual-corridor decision for a single positive-weight quadratic span."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import sys,json
from random import Random

B=((1,-2,1),(0,2,-2),(0,0,1)) # Bernstein quadratic, ascending powers.
def add(q,r): return tuple(a+b for a,b in zip(q,r))
def dot(q,p): return sum(a*b for a,b in zip(q,p))
def at(q,t): return q[0]+t*(q[1]+t*q[2])
def frame(aff,p):
    M,b=aff
    return tuple(dot(row,p)+c for row,c in zip(M,b))
def compose(a,b):
    M,u=a
    N,v=b
    return tuple(tuple(dot(r,c) for c in zip(*N)) for r in M),frame(a,v)
def envelope(points,weights,aff,K,n,lim):
    # Nonnegative iff the whole denominator-scaled clearance is nonnegative.
    bound=lim-max(dot(n,z) for z in K)
    return tuple(sum(w*(bound-dot(n,frame(aff,p)))*bs[j]
                    for p,w,bs in zip(points,weights,B)) for j in range(3))
def minimum(q,l,r):
    _,b,a=q
    candidates=[l,r]
    if a>0 and l< (s:=F(-b,2*a)) <r: candidates.append(s)
    t=min(candidates,key=lambda x:at(q,x))
    return at(q,t),t
def as_rational(u):
    q=tuple(F(s) for s in u.split())
    return q[:2],q[2]
def read_dump(path):
    ls=Path(path).read_text().strip().splitlines()
    assert ls[3:]==['three transforms: node converted, world control points unchanged']
    ps,ws=zip(*(as_rational(l) for l in ls[:3]))
    return ps,ws
def check(ps,ws,T,K,H,ell):
    qs=[envelope(ps,ws,T,K,n,c) for n,c in H]
    assert qs and all(w>0 for w in ws) and 0<=ell<=1 and K
    v,(i,s)=min((d,(j,u)) for j,q in enumerate(qs) for d,u in [minimum(q,ell,F(1))])
    return v>=0,(i,s,v)
def value(points,weights,t):
    bs=((1-t)**2,2*t*(1-t),t*t)
    ws=[w*b for w,b in zip(weights,bs)]
    return tuple(sum(x*k for x,k in zip(ds,ws))/sum(ws) for ds in zip(*points))
def direct_one(p,w,T,K,H,ell):
    # Independent construction: for each actual K vertex and face recover
    # the scalar quadratic from three geometric evaluations, not control coefficients.
    for z,(n,c) in product(K,H):
        def f(t):
            xy=frame(T,value(p,w,t))
            den=sum(wi*bi for wi,bi in zip(w,((1-t)**2,2*t*(1-t),t*t)))
            return (c-dot(n,tuple(a+b for a,b in zip(xy,z))))*den
        g,h,k=f(F(0)),f(F(1,2)),f(F(1))
        a=2*(g+k-2*h);b=k-g-a
        # Endpoint negative, or strict interior root minimum with negative numerator.
        if f(ell)<0 or k<0 or (a>0 and 2*a*ell < -b < 2*a and 4*a*g < b*b):
            return False
    return True
ID=(((1,0),(0,1)),(0,0))
ROT=(((-1,0),(0,-1)),(8,0))
CORRIDOR=[((0,1),1),((1,0),9),((-1,0),1),((0,-1),3)]
K0=[(0,0)]
def replay(ps,ws):
    good,_=check(ps,ws,ID,K0,CORRIDOR,F(0))
    failed,wit=check(ps,ws,ROT,K0,CORRIDOR,F(0))
    assert good and not failed and wit==(0,F(1,2),-1)
    assert all(dot(n,frame(ROT,p))<=c for p in (ps[0],ps[-1]) for n,c in CORRIDOR)
    assert frame(ROT,ps[-1])==ps[-1]
    assert not check(ps,ws,ROT,K0,CORRIDOR,F(85,100))[0]
    assert check(ps,ws,ROT,K0,CORRIDOR,F(86,100))[0]
    # A second observed change tightens the permitted y. Future suffix proof must change.
    tightened=[((0,1),F(1,2)),*CORRIDOR[1:]]
    assert not check(ps,ws,ROT,K0,tightened,F(86,100))[0]
    assert check(ps,ws,ROT,K0,tightened,F(94,100))[0]
    pos=[(0,0),(2,2),(4,0)]
    assert check(pos,ws,ID,K0,CORRIDOR,F(0))[0] # interior meets y=1 tangentially
    assert any(dot(CORRIDOR[0][0],p)>CORRIDOR[0][1] for p in pos)
    assert not check(pos,ws,ID,K0,[((0,1),F(99,100))],F(0))[0]
    K=[(-1,0),(0,1),(1,0)]
    assert not check(pos,ws,ID,K,CORRIDOR,F(0))[0]
    # Two observed half-turns transport the original frame again.
    assert compose(ROT,ROT)==ID
    assert check(ps,ws,compose(ROT,ROT),K0,CORRIDOR,F(0))[0]
    R=Random(534)
    verdicts=accepted=0
    for _ in range(400):
        p=[(R.randrange(-6,7),R.randrange(-6,7)) for _ in range(3)]
        w=[R.randrange(1,5) for _ in p]
        n=(R.randrange(-2,3),R.randrange(-2,3))
        H=[(n,R.randrange(-5,6)),((1,0),R.randrange(-5,6))]
        K=[(R.randrange(-3,4),R.randrange(-3,4)) for _ in range(3)]
        T=(R.choice((ID[0],ROT[0],((0,-1),(1,0)))),(R.randrange(-2,3),R.randrange(-2,3)))
        for ell in (F(0), F(2,5),F(1)):
            c,wit=check(p,w,T,K,H,ell)
            assert c==direct_one(p,w,T,K,H,ell)
            if not c:
                i,t,_=wit
                pos=frame(T,value(p,w,t))
                n,limit=H[i]
                z=max(K,key=lambda z:dot(n,z))
                assert dot(n,pos)+dot(n,z)>limit
            accepted+=c
            verdicts+=1
    return dict(matched_verdicts=verdicts,accepted=accepted,endpoint_only_false_pass=True,
                reported_progress_85_refused_86_passed=True,
                second_change_invalidates_old_suffix=True,convex_hull_false_refusal=True)
if __name__=='__main__':
    print(json.dumps(replay(*read_dump(sys.argv[1])),sort_keys=True,indent=2))
