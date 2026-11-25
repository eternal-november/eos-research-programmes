"""Exact offline observation summary vs direct finite protocols, no live systems."""
from itertools import combinations, product
from collections import defaultdict
from pathlib import Path
import json, random, sys

def partition(n,k):
    """Restricted growth words: all partitions into at most k classes."""
    def gen(cur):
        if len(cur)==n:
            yield cur
            return
        for a in range(min(k,2+max(cur,default=-1))):
            yield from gen(cur+(a,))
    yield from gen(())

def exact_masks(worlds, p):
    cells={}
    for q,r,ok in worlds:
        cells[q,r]=cells.get((q,r),(1<<p)-1)&ok
    return cells
def minimal_edges(n,p,cells):
    es=set()
    rs={r for _,r in cells}
    for r in rs:
        cs=[q for q in range(n) if (q,r) in cells]
        for j in range(1,min(p,len(cs))+1):
            for vs in combinations(cs,j):
                s=frozenset(vs)
                if any(e<=s for e in es):continue
                ok=(1<<p)-1
                for q in vs:ok &= cells[q,r]
                if not ok:es.add(s)
    return {e for e in es if not any(f<e for f in es)}
def color_ok(edges,b):
    return all(len({b[v] for v in e})>1 for e in edges)
def direct_one(worlds,n,rn,p,k):
    for enc in product(range(k),repeat=n):
        slots_list=sorted({(r,enc[q]) for q,r,_ in worlds})
        slots={v:i for i,v in enumerate(slots_list)}
        for dec in product(range(p),repeat=len(slots)):
            if all((ok>>dec[slots[r,enc[q]]])&1 for q,r,ok in worlds):
                return True
    return False
def restricted_chromatic(n,es):
    for k in range(1,n+1):
        if any(color_ok(es,b) for b in partition(n,k)):return k
    return None

def duty(q,ctx,port,t_msg=None,code=None,decoder=None,backstop=False):
    """One concrete staged, exclusive sample movement. Ticks model cut order."""
    inventory={"staging":1,"branch":0,"destination":0}
    if code is not None and t_msg is not None and t_msg<=1:
        port=decoder[ctx,code[q]]
    if not (0<=port<len(ctx)+int(backstop)):
        return False,inventory
    # Tick 1 launches the one branch. Tick 2 reaches its distinct physical port.
    inventory["staging"]-=1
    inventory["branch"]+=1
    # Tick 3 a powered hoist on the committed branch can effect delivery.
    if port==len(ctx) and backstop or ctx[port]!=q:
        inventory["branch"]-=1
        inventory["destination"]+=1
    assert sum(inventory.values())==1
    return inventory["destination"]==1,inventory

def ctxworlds(n,edges):
    return [(q,j,sum(1<<a for a in range(len(e)) if duty(q,e,a)[0]))
            for j,e in enumerate(edges) for q in range(n)]
def profile(n,p,worlds):
    return minimal_edges(n,p,exact_masks(worlds,p))

def verify():
    rng=random.Random(4913)
    control=timed=uniform=direct=0
    for n in range(3,6):
        pool=list(combinations(range(n),3))
        for mask in range(1<<len(pool)):
            es=[e for i,e in enumerate(pool) if mask>>i&1]
            gotten=profile(n,3,ctxworlds(n,es))
            target={frozenset(e) for e in es}
            assert gotten==target
            # A separate raw response check for every unrestricted encoder partition.
            for b in partition(n,n):
                raw=all(any(all(duty(q,e,a)[0] for q in range(n) if b[q]==x)
                        for a in range(3)) for e in es for x in set(b))
                assert raw==color_ok(gotten,b)
                control+=1
            uniform+=1
    for n,p in [(3,3),(5,3),(7,3),(8,4),(7,5)]:
        es=list(combinations(range(n),p))
        h=profile(n,p,ctxworlds(n,es))
        assert not any(len(e)<p for e in h)
        assert restricted_chromatic(n,h)==(n+p-2)//(p-1)
    for _ in range(120):
        n,rn,p=3,2,3
        ws=[]
        for q,r in product(range(n),range(rn)):
            for _ in range(rng.randrange(3)):
                ws.append((q,r,rng.randrange(1<<p)))
        h=profile(n,p,ws)
        for k in range(1,4):
            assert any(color_ok(h,b) for b in partition(n,k))==direct_one(ws,n,rn,p,k)
            direct+=1
    e=(0,1,2)
    b=(0,0,1)
    decode={(e,0):2,(e,1):0}
    for latency,q in product(range(5),range(3)):
        assert duty(q,e,0,latency,b,decode)[0]==(latency<=1 or q!=0)
        assert duty(q,e,3,latency,None,None,backstop=True)[0]
        timed+=1
    fano=[(0,1,2),(0,3,4),(0,5,6),(1,3,5),(1,4,6),(2,3,6),(2,4,5)]
    assert restricted_chromatic(7,profile(7,3,ctxworlds(7,fano)))==3
    return {"cells_checked_against_raw_protocols":direct,
            "hypergraphs_exhausted":uniform,"raw_timed_policy_groups_checked":control,
            "deadline_controls":timed,
            "three_branch": {"chosen_partition":b,"first_message_must_arrive_by":1,
                             "physical_delivery_tick":3,"minimum_alphabet":2}}
if __name__=='__main__':
    r=json.dumps(verify(),sort_keys=True,indent=2)+'\n'
    if len(sys.argv)>1:Path(sys.argv[1]).write_text(r)
    else:print(r,end='')
