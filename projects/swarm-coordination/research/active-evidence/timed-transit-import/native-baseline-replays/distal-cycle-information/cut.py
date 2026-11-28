"""Exact held-in information-cut model over the complete published graph."""
from collections import deque,Counter
from functools import cache
from itertools import product
import json,re,sys
from xml.etree import ElementTree
from pathlib import Path

P=Path(sys.argv[1])
raw=(P/"world.dot").read_text()
V=list(map(int,re.findall(r'^\s*(\d+)\s+\[label=".*?"\];',raw,re.M)))
E={tuple(sorted(map(int,ab))) for ab in re.findall(r'(\d+)\s*--\s*(\d+)\s*\[label=\d+\]',raw)}
K=((115,118),(117,119))
S,G=103,132
assert len(V)==158 and len(E)==163 and all(k in E for k in K)

def graph(deletion=()):
    A={i:set() for i in V}
    for a,b in E-set(deletion):A[a].add(b);A[b].add(a)
    return A

def dist(A,start,stop=()):
    d={x:0 for x in start}
    queue=deque(start)
    halted=set(stop)
    while queue:
        v=queue.popleft()
        if v in halted:continue
        for w in A[v]:
            if w not in d:d[w]=d[v]+1;queue.append(w)
    return d

A0=graph()
direct=[graph((k,)) for k in K]
shared=graph(K)
dg=[dist(a,[G]) for a in direct]
ds=[dist(a,[S]) for a in direct]
assert len(dist(A0,[S]))==158
assert all(len(x)==158 for x in dg)
assert [x[G] for x in ds]==[10,10]
assert G not in dist(shared,[S])
assert all(dist(graph(((103,104),)),[103])[104]==19 for _ in (0,))

def remaining(v,seen,case,service):
    # Unit traversal, optional separately named service tick at the goal,
    # then return to home. Report receipt is not credited by passing a node.
    return ds[case][v] if seen else dg[case][v]+service+ds[case][G]

def reveal_at(r):
    return {v for v,d in dist(A0,[*K[0],*K[1]]).items() if d<=r}

def solved(sense,remote,service):
    remote=10000 if remote is None else remote
    @cache
    def go(v,t):
        if v in sense or t>=remote:
            return t+max(remaining(v,False,w,service) for w in (0,1))
        if t>31:return 10000
        return min(go(q,t+1) for q in shared[v]|{v})
    return go(S,0)

def independent(sense,remote,service):
    # Any prefix that avoids a local observing vertex must be a common
    # path. Distance search stops at the first local observation.
    prefixes=dist(shared,[S],sense)
    local=[t+max(remaining(v,False,w,service) for w in (0,1))
           for v,t in prefixes.items() if v in sense]
    candidates=local[:]
    if remote is not None:
        candidates += [remote+max(remaining(v,False,w,service) for w in (0,1))
                       for v,t in prefixes.items() if t<=remote and v not in sense]
    return min(candidates)

def horizon(sense,remote,service):
    # Explicit safety/service game: unknown route uses common edges;
    # every compatible observation branch must settle before deadline.
    # Fixed known world is independently checked with BFS remaining cost.
    def try_with(T):
        @cache
        def win(v,t):
            if t>T:return False
            if v in sense or (remote is not None and remote<=t):
                return all(t+remaining(v,False,w,service)<=T for w in (0,1))
            return any(win(q,t+1) for q in shared[v]|{v})
        return win(S,0)
    return try_with

def timer():
    values={}
    for radius,service,remote in product(range(5), (0,1,2), (*range(15),None)):
        sense=reveal_at(radius)
        v=solved(sense,remote,service)
        assert v==independent(sense,remote,service)
        ok=horizon(sense,remote,service)
        assert ok(v) and not ok(v-1)
        assert v==20+service+min(2*max(0,4-radius),100 if remote is None else remote)
        values[(radius,service,str(remote))]=v
    return values

def main():
    z=ElementTree.parse(P/"world.sdf")
    positions={int(e.findtext("name")[5:]):list(map(float,e.findtext("pose").split()[:3]))
               for e in z.findall(".//include")
               if (e.findtext("name") or "").startswith("tile_")}
    assert len(positions)==157
    values=timer()
    distribution=Counter(map(len,A0.values()))
    # Connected bridge check via unit adjacency, independent of edge labels.
    bridges={e for e in E if len(dist(graph((e,)),[S]))!=158}
    assert len(bridges)==101 and distribution=={1:9,2:130,3:19}
    print(json.dumps(dict(vertices=len(V),edges=len(E),bridges=len(bridges),
      start=positions[S],goal=positions[G],gates={str(k):[positions[q] for q in k] for k in K},
      scenarios=len(values),service1_cutoff_table={str(r):[values[r,1,str(t)] for t in range(9)] for r in range(5)},
      no_remote={str(r):values[r,1,"None"] for r in range(5)}),sort_keys=True))
if __name__=="__main__":main()
