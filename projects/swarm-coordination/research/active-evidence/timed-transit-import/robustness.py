"""Start-window uncertainty; preserve same-history duration/outage pairing."""
from macro import *
from itertools import product

def robust_box(path,bounds,outages):
    # Integer durations, every combination of values in the input box
    # admitted. All supported duration executions are noninterruptible.
    lo_o=hi_o=0
    W=[]
    for a,b in zip(path,path[1:]):
        lo,hi=bounds[a,b]
        assert 1<=lo<=hi
        for l,u in outages.get((a,b),()):
            W.append((max(0,l-hi_o-hi+1),u-lo_o))
        lo_o+=lo
        hi_o+=hi
    return (lo_o,hi_o),merged(W)

def robust_worlds(path,bundles):
    # Each element is a certified matched box/outage law, not a list of
    # durations to be crossed with each unrelated outage family.
    D=[]
    W=[]
    for box,e in bundles:
        d,w=robust_box(path,box,e)
        D.append(d);W.extend(w)
    return (min(a for a,b in D),max(b for a,b in D)),merged(W)

def tests():
    p=tuple(range(4));ids=tuple(zip(p,p[1:]))
    options=[(1,1),(1,2),(1,3),(2,3)]
    count=0
    for rngs,k,a,w in product(product(options,repeat=3),range(3),range(8),(1,2,4)):
        B=dict(zip(ids,rngs));O={ids[k]:[(a,a+w)]}
        _,blocked=robust_box(p,B,O)
        D=[dict(zip(ids,ds)) for ds in product(*(range(l,u+1) for l,u in rngs))]
        for t in range(12):
            assert can_enter(t,blocked)==all(physical(p,d,O,t) for d in D)
            count+=1
    print(count,"robust occupancy comparisons with all integer duration executions")
    p=(0,1,2)
    fast={(0,1):(1,1),(1,2):(1,1)}
    slow={(0,1):(3,3),(1,2):(1,1)}
    late={(1,2):[(3,4)]}
    early={(1,2):[(1,2)]}
    assert can_enter(0,robust_worlds(p,[(fast,late),(slow,early)])[1])
    assert not can_enter(0,robust_worlds(p,[(fast,late),(slow,early),(fast,early)])[1])
    print("crossing different worlds' durations and outages invents an unsafe transit")
    d={(0,1):1,(1,2):1};o={(0,1):[(1,5)],(1,2):[(1,2)]}
    assert not any(physical(p,d,o,t) for t in range(3))
    assert physical((0,1),d,o,0) and physical((1,2),d,o,2)
    print("if mid-corridor waiting is permitted, commitment compression is incomplete")
if __name__=="__main__":tests()
