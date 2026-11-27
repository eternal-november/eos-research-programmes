"""Held-in source-topology replay. Timing, equipment and sensing are authored."""
import argparse
from itertools import combinations, product
from functools import lru_cache
import json
from pathlib import Path

X,U,V,R,T,D,E=(11,28),(11,29),(12,28),(12,29),(10,29),(11,27),(13,28)
ANCHOR="7e77737096356184e1380fddbbbda42d94869362"

def edge(p,q,P):
    return p in P and q in P and sum(abs(a-b) for a,b in zip(p,q))==1

def geometry(topology):
    P={(x,y) for x,y,_ in json.loads(Path(topology).read_text())["occupied"]}
    for path in ((X,D),(X,V,E),(U,R,U,T)):
        assert all(edge(p,q,P) for p,q in zip(path,path[1:]))
    assert len({X,U,V,R,T,D,E})==7 and edge(X,U,P)
    # Equipment at R operates the final traversal V->E; this is not a
    # derived optical, RF, or electrical capability of the site.

def realized(physical, blackout, clear, release, first_hold, attempts, ok, H):
    """Safety/mission check on absolute ticks; standing rules fit local cuts."""
    if not physical:
        exit_a=2
    else:
        # Old inspection X is completed and report ready at 1.
        # Enter V only with hold continuing through crossing into E.
        if first_hold!=2 or release<clear:
            exit_a=None
        else:
            exit_a=clear
    exit_m=(release+2) if physical and first_hold==2 and release is not None else 2
    # Primary publication at 1 is ACKed at 2; otherwise A retains the copy.
    arrivals=[t+1 for t in attempts if t>=exit_m and t in ok]
    delivery=2 if not blackout else min(arrivals,default=None)
    return dict(inspection=1, independent_job=2, egress_a=exit_a,
                egress_m=exit_m, confirmed_delivery=delivery,
                complete=exit_a is not None and exit_a<=H and exit_m<=H
                and delivery is not None and delivery<=H)

def arrival(clear, sensor, worst_clear):
    # M must not infer physical clearance from no reading until the declared
    # latest-clear bound. Only the release time is exported to its uploader.
    return (clear if sensor else worst_clear)+2

def hitting(worlds,H,sensor,worst_clear):
    by_arrival={}
    for clear,good in worlds:
        a=arrival(clear,sensor,worst_clear)
        by_arrival.setdefault(a,[]).append(good)
    policy={}
    for a, goods in by_arrival.items():
        slots=range(a,H)
        for k in range(len(slots)+1):
            choice=next((S for S in combinations(slots,k)
                         if all(set(S)&good for good in goods)),None)
            if choice is not None:
                policy[a]=choice
                break
        else:
            return None
    return policy

def direct(worlds,H,sensor,worst_clear,budget):
    # Timed return/data-mule + physical predecessor with independent local
    # observations. Explicit policy game: wait or attempt each slot. A
    # receipt terminates; failures remove worlds. No hidden state to policy.
    groups={}
    for c,g in worlds:
        groups.setdefault(arrival(c,sensor,worst_clear),set()).add(frozenset(g))
    for start, goods in groups.items():
        @lru_cache(None)
        def win(t,remaining,L):
            if not L: return True
            if t>=H or remaining<=0: return False
            return win(t+1,remaining,L) or win(t+1,remaining-1,
                    frozenset(g for g in L if t not in g))
        if not win(start,budget,frozenset(goods)): return False
    return True

def trace(worlds,H,sensor,worst_clear,policy):
    rows=[]
    for c,g in worlds:
        a=arrival(c,sensor,worst_clear)
        actions=[]
        for t in policy[a]:
            actions.append(t)
            if t in g: break
        z=realized(True,True,c,a-2,2,actions,g,H)
        assert z["complete"]
        rows.append((c,sorted(g),a,actions,z))
    return rows

def suite():
    H=8
    controls={}
    for p,b in product((False,True),repeat=2):
        controls[f"physical={p},radio={b}"]=realized(
            p,b,4,4 if p else None,2 if p else None,
            (6,) if p else (2,), {2,6,7}, H)
    assert all(z["complete"] for z in controls.values())
    independent=realized(True,True,4,2,0,(2,),{2},H)
    assert independent["confirmed_delivery"]==3 and independent["egress_a"] is None
    # The nominal egress interlock is not a generic scheduler permission.
    observed=((4,{6}),(5,{7}))
    stale=((4,{6}),(4,{7}),(5,{7}))
    product_law=tuple(product((4,5),({6},{7})))
    p=hitting(observed,H,True,5); assert p=={6:(6,),7:(7,)}
    assert hitting(observed,H,False,5) is None
    q=hitting(stale,H,True,5); assert q=={6:(6,7),7:(7,)}
    assert hitting(product_law,H,True,5) is None
    # No handoff sensor: synthetic missing reading does not permit departure.
    # Upper bound 5 is physical only for worlds in this envelope.
    rows={"controls":controls,"deliver_only":independent,
          "joint_one_attempt":trace(observed,H,True,5,p),
          "joint_two_attempts":trace(stale,H,True,5,q),
          "wait_to_latest_clear_loses_early_only":True,
          "independently_crossed_law_infeasible":True}
    count=num_safe=0
    for n in range(1,4):
        H=6+n
        C=range(4,7)
        masks=[{t for t in range(6,H) if (i>>(t-6))&1}
               for i in range(1<<n)]
        # Two independently chosen traces, including exact duplicates and
        # traces whose uploader offers no primary service at all.
        for a,b,c,d,sensor in product(C,C,masks,masks,(False,True)):
            w=((a,c),(b,d))
            x=hitting(w,H,sensor,6)
            if x is not None:
                trace(w,H,sensor,6,x)
                num_safe+=1
            for k in range(n+1):
                assert direct(w,H,sensor,6,k)==(
                    x is not None and max(map(len,x.values()))<=k)
                count+=1
    rows.update(direct_agreement=count, checked_positive_policies=num_safe)
    return rows

if __name__=="__main__":
    ap=argparse.ArgumentParser()
    ap.add_argument("topology")
    geometry(ap.parse_args().topology)
    print(json.dumps(suite(),indent=2,sort_keys=True))
