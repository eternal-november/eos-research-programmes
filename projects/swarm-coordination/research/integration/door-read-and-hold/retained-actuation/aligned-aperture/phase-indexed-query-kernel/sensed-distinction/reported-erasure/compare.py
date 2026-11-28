"""Bounded, causally reported read erasure on the aperture trace family."""
from functools import cache
from itertools import product, combinations
import json,sys
from pathlib import Path

def load(path):
    data={}
    for line in Path(path).read_text().splitlines():
        k,t,n,*v=line.split()
        data[tuple(map(int,(k,t,n)))]=[tuple(map(int,p.split(":"))) for p in v]
    return [data[k] for k in ((3,0,0),(3,3,3),(5,0,0),(5,5,2))]

def suite(traces, labels, horizon, sensor):
    pairs=[(a,b) for a,b in combinations(range(len(traces)),2) if labels[a]!=labels[b]]
    @cache
    def good(times):
        if not times:return False
        if sensor=="mode":
            return all(any(traces[a][t][1]!=traces[b][t][1] for t in times) for a,b in pairs)
        # epsilon=7/4; strictly more than 4 epsilon separates closed sets.
        span=[max(v)-min(v) for a,b in pairs
              for v in [[traces[a][t][0]-traces[b][t][0] for t in times]]]
        return min(span)>7

    @cache
    def plan(next_slot,left,lost,read):
        if good(read):return True
        if not left:return False
        for i in range(next_slot,horizon):
            ok=plan(i+1,left-1,lost,read+(i,))
            erasure=plan(i+1,left-1,lost-1,read) if lost else None
            if ok and (erasure or erasure is None):
                return [i+1,ok,erasure]
        return False

    def leaves(tree, sofar=(), budget=1):
        if tree is True:
            assert good(sofar)
            return [list(i+1 for i in sofar)]
        slot,a,b=tree
        assert not sofar or sofar[-1]<slot-1
        hit=leaves(a,sofar+(slot-1,),budget)
        if budget:
            assert b
            hit+=leaves(b,sofar,budget-1)
        else:assert b is None
        return hit

    robust=[]
    for n in range(1,horizon+1):
        for z in combinations(range(horizon),n):
            if all(good(z[:i]+z[i+1:]) for i in range(n)):
                robust.append([i+1 for i in z]);break
        if robust:break
    fixed=robust[0] if robust else None
    result=next(((n,r) for n in range(1,horizon+1) if (r:=plan(0,n,1,()))),None)
    # A completely sampled mode history cannot save two different tags
    # if all their observations differ in at most one slot.
    collision=next(([a,b,[i+1 for i in range(horizon) if traces[a][i][1]!=traces[b][i][1]]]
                    for a,b in pairs if sum(traces[a][i][1]!=traces[b][i][1] for i in range(horizon))<=1),None)
    if result:
        n,tree=result
        l=leaves(tree)
        return dict(adaptive=n,tree=tree,success=l,fixed=fixed,collision=collision)
    return dict(adaptive=None,fixed=fixed,collision=collision)

def fixed_refutations(traces,horizon,n,labels):
    pairs=[(a,b) for a,b in combinations(range(len(traces)),2) if labels[a]!=labels[b]]
    proofs=[]
    for z in combinations(range(horizon),n):
        for i in range(n):
            times=z[:i]+z[i+1:]
            found=False
            for a,b in pairs:
                A=[4*traces[a][t][0] for t in times]
                B=[4*traces[b][t][0] for t in times]
                diff=[x-y for x,y in zip(A,B)]
                if max(diff)-min(diff)>28:continue
                # e=7 quarter-units. Offset choices below really generate
                # one common transcript from both histories.
                bias=-14-min(diff)
                A=[x+bias for x in A]
                y=[max(x,z)-7 for x,z in zip(A,B)]
                assert all(abs(x-v)<=7 for source in (A,B) for x,v in zip(source,y))
                proofs.append([list(t+1 for t in z),z[i]+1,[a,b],y])
                found=True
                break
            if found:break
        assert found
    return proofs

def main():
    traces=load(sys.argv[1]); rows={}
    for purpose,labels in (("profile",[0,0,1,1]),("action",[0,1,1,1])):
        for horizon,sensor in product((5,8,10),("numeric","mode")):
            rows[f"{purpose}/{horizon}/{sensor}"]=suite(traces,labels,horizon,sensor)
    def sizes(key):
        a=rows[key]
        return a["adaptive"], None if a["fixed"] is None else len(a["fixed"])
    assert sizes("action/8/numeric")== (3,4)
    assert sizes("profile/8/numeric")== (4,5)
    assert sizes("profile/10/numeric")== (3,4)
    assert sizes("action/5/mode")== (2,2)
    assert sizes("profile/10/mode")== (None,None)
    assert rows["profile/10/mode"]["collision"] is not None
    checks={
         "action/8/3":fixed_refutations(traces,8,3,[0,1,1,1]),
         "profile/8/4":fixed_refutations(traces,8,4,[0,0,1,1]),
         "profile/10/3":fixed_refutations(traces,10,3,[0,0,1,1])}
    assert [len(v) for v in checks.values()]==[56,70,120]
    print(json.dumps(dict(results=rows,fixed_refutations=checks),sort_keys=True))
if __name__=="__main__":main()
