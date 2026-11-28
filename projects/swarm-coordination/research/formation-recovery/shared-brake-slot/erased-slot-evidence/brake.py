"""Integer exact replay for one lost exclusive brake command."""
from functools import lru_cache
from itertools import product

# state = (first speed,second speed,twice relative displacement)
# Sign + moves gap upward by braking first; choose orientation consistently.
def step(x,a,erased,clip):
    p,f,g=x
    if not erased and a==1 and not p and not clip:return None
    if not erased and a==-1 and not f and not clip:return None
    s=(int(a==1 and p>0)-int(a==-1 and f>0)) if not erased else 0
    return p-int(s==1),f-int(s==-1),g+2*(f-p)+s

def search(v,d,H,cap,clip=True,worlds=None,rtn=False):
    es=tuple(range(-1,H)) if worlds is None else tuple(worlds)
    assert cap>=0
    pol={}
    @lru_cache(None)
    def ok(t,xs):
        if any(abs(g)>cap for _,(_,_,g) in xs):return False
        left=H-t
        if all(p==f==0 for _,(p,f,g) in xs):return True
        if left==0:return False
        for e,(p,f,g) in xs:
            if p+f>left-int(e>=t):return False
        for a in (1,-1,0):
            buckets={}
            for e,x in xs:
                n=step(x,a,e==t,clip)
                if n is None or abs(n[2])>cap:break
                outcome=e if e>=0 and e+d+1<=t+1 else -1
                buckets.setdefault(outcome,[]).append((e,n))
            else:
                children=[tuple(z) for z in buckets.values()]
                if all(ok(t+1,tgt) for tgt in children):
                    if rtn:pol[t,xs]=(a,children)
                    return True
        return False
    start=tuple((e,(v,v,0)) for e in es)
    result=ok(0,start)
    return (result,pol,start) if rtn else result

def minimum(v,d,H,clip=True,worlds=None):
    # no speed can exceed v, so this bounds the reachable doubled gap
    cap=2*v*H
    if not search(v,d,H,cap,clip,worlds):return None
    lo,hi=0,cap
    while lo<hi:
        m=(lo+hi)//2
        if search(v,d,H,m,clip,worlds):hi=m
        else:lo=m+1
    return lo

if __name__=='__main__':
    for v in range(1,9):
        print(v,[(d,minimum(v,d,2*v+1),minimum(v,d,2*v+1,False)) for d in range(v+2)],flush=True)
