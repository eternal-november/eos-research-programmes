"""Fixed joint erasure support, preserving actual costs of failed acquisition."""
from charged import Source,SHARED,SEPARATE
from itertools import product
from functools import cache
from random import Random

def antichain(W):
    W=set(W)
    return tuple(sorted(q for q in W if not any(
         q!=r and q[0]<=r[0] and q[1]<=r[1] for r in W)))

def child(W,act):
    return tuple((k-int(act==0),v-int(act==1)) for k,v in W
                 if (k if act==0 else v)>0)

def plan(z,modes,E,L,guard_callback=True,independent=True,reduce=True):
    convert=antichain if reduce else lambda x:tuple(sorted(set(x)))
    used={}
    @cache
    def go(W,t,clean,B):
        if t>=E or clean>L:return False
        for act in range(2):
            nxt=convert(child(W,act))
            if act==0:
                if nxt and not z.guard:continue
                a=max(t,clean);b=a+1;c=0
                off=b+z.cooldown if z.cooldown else clean
            else:
                if B<z.battery_cost:continue
                a=t if independent else max(t,clean)
                b=a+z.spare_dur;c=z.battery_cost
                off=clean
            if b>E:continue
            if not nxt or go(nxt,b,off,B-c):
                used[W,t,clean,B]=(act,a,b,nxt,off,B-c)
                return True
        return False
    W=convert(modes);s=(W,0,0,z.battery)
    if not go(*s):return None
    if not guard_callback:return True
    ans=[]
    while True:
        act,a,b,W,off,B=used[s]
        ans.append((act,a,b,W,off,B))
        if not W:break
        s=(W,b,off,B)
    return ans

def direct(z,W,E,L,ind=True):
    # Independent nonadaptive enumeration of the unique no-cue prefix.
    # Success prefixes always stop acquisition and preserve old cleanup.
    max_path=max(a+b for a,b in W)+1
    for span in range(1,max_path+1):
        for code in product(range(2),repeat=span):
            time=0;clean=[];B=z.battery
            candidates=tuple(W)
            for k,act in enumerate(code):
                last=k+1==span
                Y=child(candidates,act)
                if act==0 and Y and not z.guard:break
                if act:
                   B-=z.battery_cost
                   if B<0:break
                while (act==0 or not ind) and time in clean:time+=1
                d=z.spare_dur if act else 1
                assert (act==1 and ind) or not any(q in clean for q in range(time,time+d))
                time+=d
                if time>E:break
                if not Y and last:return True
                if not Y or last:break
                if act==0:clean.extend(range(time,time+z.cooldown))
                if any(q>=L for q in clean):break
                candidates=Y
    return False

def checks():
    rng=Random(280447);j=0
    for _ in range(3500):
        X=tuple((rng.randrange(3),rng.randrange(3)) for _ in range(rng.randrange(1,6)))
        d,s,c,g,B=rng.randrange(4),rng.randrange(1,4),rng.randrange(1,3),bool(rng.randrange(2)),rng.randrange(5)
        z=Source(d,s,c,g,0,B)
        E,L=rng.randrange(1,12),rng.randrange(1,12)
        ind=bool(rng.randrange(2))
        a=bool(plan(z,X,E,L,False,ind,True))
        b=bool(plan(z,X,E,L,False,ind,False))
        assert a==b==direct(z,X,E,L,ind),(z,X,E,L,ind)
        j+=1
    print(j,"source-coupled frontier vs direct schedule enumerations")
    z=Source(3,2,1,False,0,1)
    W=((1,0),(0,1))
    A=plan(z,W,3,3)
    assert A and [a for a,*_ in A]==[1,0]
    assert not plan(z,W,2,3)
    assert not plan(z,[(1,1)],10,3)
    print("source-coupled failure law: one paid failure followed by safe unguarded shared try; exact time 3")
    print("same marginals with independent worst-case support cannot make that guarantee")
if __name__=="__main__":checks()
