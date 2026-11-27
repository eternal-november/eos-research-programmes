"""Compile static corridor hardware profiles; execute event-triggered jobs."""
from itertools import product
from random import Random
import heapq
import json

# Each mode selects a fixed, independently usable port at each end.
# Semantic modes can include more fields after checking the decoder.
M=((0,0),(0,1),(1,0),(1,1))

def pair(a,b,g,P):
    return P>=2*g or M[a][1]!=M[b][0]

def compose(a,b):
    nexts={}
    for q,k in b:
        nexts.setdefault(q,[]).append(k)
    return {(i,k) for i,j in a for k in nexts.get(j,())}

def export(allowed,g,P):
    if P<g:
        return set()
    t={(m,m) for m in allowed[0]}
    for rights in allowed[1:]:
        t=compose(t,{(p,q) for p in range(len(M)) for q in rights if pair(p,q,g,P)})
    return t

def synth(allowed,g,P):
    if P<g:
        return None
    layers=[{m:None for m in allowed[0]}]
    for rights in allowed[1:]:
        out={}
        for q in rights:
            for p in layers[-1]:
                if pair(p,q,g,P):
                    out[q]=p
                    break
        layers.append(out)
    if not layers[-1]:
        return None
    p=next(iter(layers[-1]))
    chosen=[]
    for layer in reversed(layers):
        chosen.append(p)
        p=layer[p]
    return tuple(reversed(chosen))

def directly_conflicts(m,g,P):
    # Test the forced full-duration realization on two offers. This
    # independent feasibility comparator uses interval occupancy,
    # without consulting the relational composition or its predicate.
    busy={}
    for k in (0,1):
        for i,ax in enumerate(m):
            start=k*P+i*g
            for robot,port in ((i,M[ax][0]),(i+1,M[ax][1])):
                records=busy.setdefault((robot,port),[])
                if any(max(a,start)<min(b,start+g) for a,b in records):
                    return True
                records.append((start,start+g))
    return False

def main():
    checked=0
    masks=[tuple(m for m in range(4) if bit>>m&1) for bit in range(1,16)]
    rng=Random(7101)
    # Every two-site menu, next exhaustive three-site menus with three
    # possible configurations; then nonempty wider menus and long chains.
    cases=list(product(masks,repeat=2))
    subset=[tuple(m for m in range(3) if bit>>m&1) for bit in range(1,8)]
    cases+=list(product(subset,repeat=3))
    cases+=[(m,) for m in masks]
    cases.extend(tuple(rng.choice(masks) for _ in range(4)) for i in range(240))
    for menus,g,P in product(cases,(1,3),(0,1,2,3,5,6,8)):
        brute=[m for m in product(*menus) if not directly_conflicts(m,g,P)]
        assert {(x[0],x[-1]) for x in brute}==export(menus,g,P)
        picked=synth(menus,g,P)
        assert (picked is None)==(not brute)
        if picked is not None:
            assert picked in brute
        checked+=1

    # Independent event replay: agents do not see wall-time on the
    # heap. Each observes a qualified predecessor latching event and
    # its own relative timer; the evaluator advances actual elapsed time.
    events=0
    for g in (1,2,4):
      for P in (g,2*g-1,2*g,3*g):
       for n in (1,2,3,8,64):
        m=synth((range(4),)*n,g,P)
        assert m is not None
        r=[0]
        for k in range(1,50):
            r.append(r[-1]+P+rng.randrange(0,g+1))
        events+=modeled_events(m,r,g,rng)
    assert synth(((0,),(0,)),3,5) is None
    assert synth(((0,),(0,)),3,6)==(0,0)
    assert synth(((0,),(2,)),3,5)==(0,2)
    # Adjacent pairs can each admit some shared mode while the chain
    # has no single shared choice for its middle edge.
    menus=((0,),(1,2),(0,))
    assert synth(menus[:2],1,1) is not None
    assert synth(menus[1:],1,1) is not None
    assert synth(menus,1,1) is None
    print(json.dumps(dict(menu_and_cadence_cases=checked,modeled_events=events,
                          port_boundary_at=6,local_pairs_do_not_compose=True),
                     sort_keys=True,indent=2))

def modeled_events(m,r,g,rng):
    q=[]; owners={}; ag={}; port_owner={}; complete=[]
    n=len(m)
    nextref=0
    def push(t,typ,stage,k):heapq.heappush(q,(t,typ,stage,k))
    for k,t in enumerate(r):
        push(t,3,0,k)
    while q:
        t,typ,i,k=heapq.heappop(q)
        a,b=M[m[i]]
        ports=((i,a),(i+1,b))
        if typ==3:
            if i==0:
                assert k not in owners
                owners[k]=i
            # The next local sender's latch was opened by its own
            # witnessed prior settlement, not by a global role number.
            assert owners[k]==i and i not in ag
            assert all(p not in port_owner for p in ports)
            ag[i]=(k,t+g)
            for p in ports:port_owner[p]=(i,k)
            push(t+rng.randint(1,g),0,i,k)
            push(t+g,1,i,k)
        elif typ==0:
            assert ag[i][0]==k and owners[k]==i
            # Physical completion qualifies the receiver as the next
            # certifier. Until publication through the scope-limited
            # latch no downstream transition consumes this result.
            owners[k]=i+1
        else:
            assert owners[k]==i+1 and ag.pop(i)==(k,t)
            for p in ports:
                assert port_owner.pop(p)==(i,k)
            if i+1==n:
                complete.append((k,t))
            else:
                push(t,3,i+1,k)
        nextref+=1
    assert not port_owner and not ag
    assert complete==[(k,t+n*g) for k,t in enumerate(r)]
    return nextref

if __name__=="__main__":main()
