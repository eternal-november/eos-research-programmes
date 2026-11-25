"""Hedged first stage, one actual authority transfer, no duplicate settlement."""
from dataclasses import dataclass
from itertools import chain,combinations,product
from integration import Custody,Cooling,World

ROUTES=('A','B')
def subsets(xs):
    return (t for n in range(len(xs)+1) for t in combinations(xs,n))

def possible(P,w,t):
    if P is Custody:
        return tuple(k for k,ok in P.plant(w,t).items() if ok)
    base,units=P.plant(w,t)
    return tuple(k for k,unit in units.items() if base+unit>=2)

def common_kernel(options,prepared,accepted,authority=True):
    # All new authority follows the observed physically valid result. The
    # earlier work/duty remains with the old supplier throughout pre-staging.
    if not authority:return None
    return next((k for k in options if k in prepared and k in accepted),None)

def envelope(P,w,slots,read,accepted):
    # The declared late-fault envelope has actual ongoing preparation from 3.
    old_exp=w.pack_end
    if old_exp<5:
        return False,0,()
    ready=possible(P,w,3)
    prepared=tuple(k for k in ROUTES if k in ready)[:slots]
    return replay(P,w,prepared,read,accepted)

def replay(P,w,prepared,read,accepted):
    assert all(k in possible(P,w,3) for k in prepared)
    events=[(3,'staged-only',prepared)]
    # On the t4 local channel a causal sensor knows which survives. Without
    # it no effect authorization, even if an omniscient schedule exists.
    actual=possible(P,w,4)
    authority=read and w.pack_end>=5
    chosen=common_kernel(actual if read else (),prepared,accepted,authority)
    if chosen is not None:
        assert chosen in possible(P,w,4) and chosen in possible(P,w,5)
        events.append((4,'continued-exactly-one',chosen))
    for k in prepared:
        if k!=chosen:events.append((4,'discarded-uncommitted',k))
    if chosen is None:
        if w.pack_end<5:return False,0,events
        events.append((5,'protected-settlement-without-service',None))
        return True,0,events
    if P==Custody:
        # Only NOW does the official holder change; two staged writes were
        # non-authoritative and consumable once. Old P never hands off twice.
        events.extend(((5,'only-official-holder',chosen),(6,'read-report',chosen)))
    else:
        base,aux=P.plant(w,5)
        assert base+aux[chosen]==2
        events.extend(((5,'only-active-pickup',chosen),(5,'verified-load-units',base+aux[chosen])))
    assert len([1 for _,x,_ in events if x.startswith('only-')])==1
    return True,1,events

def reference(P,worlds,slots,read,accepted):
    # At t3 all early histories in the family are identical; no one knows
    # the future failure branch. Enumerate both shared t3 actions and maps
    # from legitimate t4 observation cells to service decisions.
    views=tuple(sorted({possible(P,w,4) if read else () for w in worlds}))
    ok=[]
    for prepared in subsets(ROUTES):
        if len(prepared)>slots:continue
        for modes in product((None,*ROUTES),repeat=len(views)):
            policy=dict(zip(views,modes));jobs=0
            for w in worlds:
                view=possible(P,w,4) if read else ()
                chosen=policy[view]
                if w.pack_end<5 or not set(prepared)<=set(possible(P,w,3)):break
                if chosen is not None and not (read and chosen in accepted and chosen in view
                         and chosen in prepared and chosen in possible(P,w,5)):break
                jobs+=int(chosen is not None)
            else:
                ok.append(jobs)
    return max(ok,default=-1)

def main():
    count=0
    for P,slots,read,common,exp,accepted in product(
        (Custody,Cooling),range(3),(False,True),(False,True),(4,5,6), (('A',),('B',),('A','B'))):
        worlds=tuple(World(x,False,0,exp,4) for x in ('A','B','Common')[:3 if common else 2])
        result=tuple(envelope(P,w,slots,read,accepted) for w in worlds)
        if all(f for f,_,_ in result) and slots!=1:
            assert sum(s for _,s,_ in result)==reference(P,worlds,slots,read,accepted)
        else:
            # One-slot vertex policy below can use the accepted rank rather
            # than the lexicographic default, preserving that sole cohort.
            if exp>=5 and slots==1:
                chosen=next(iter(accepted))
                assert sum(replay(P,w,(chosen,),read,accepted)[1] for w in worlds)==reference(P,worlds,slots,read,accepted)
            else:
                assert reference(P,worlds,slots,read,accepted)==-1
        count+=1
    for P in (Custody,Cooling):
        worlds=tuple(World(x,False,0,5,4) for x in ROUTES)
        assert reference(P,worlds,1,True,ROUTES)==1
        assert reference(P,worlds,2,True,ROUTES)==2
        assert reference(P,worlds,2,False,ROUTES)==0
    print(count,'exact late-fault timing, reserve, authority and source controls')
    print('two staged alternatives and t4 local observation guarantee service in both single-loss worlds')
    print('one staging slot or no authorized observation precludes that same service floor')
if __name__=='__main__':main()
