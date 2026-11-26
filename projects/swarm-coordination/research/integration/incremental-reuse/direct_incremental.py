"""Matched rooted-witness repair baseline, rather than an intentionally cold search."""
from collections import defaultdict,deque
from copy import deepcopy
from reuse import Cache,bfs,change_fact,new_graph

def update_with_witnesses(old, c, e):
    new=new_graph(old,e)
    depend=defaultdict(list)
    for v,p in c.parent.items():
        if p is not None:
            depend[p].append(v)
    # Old hypotheses invalidated only where an actual proof parent is lost.
    lost={root for root in old.roots-new.roots if c.parent[root] is None}
    for u in e.out:
        lost.update(v for v in depend[u] if v not in new.out[u])
    q=deque(lost)
    while q:
        p=q.popleft()
        for v in depend[p]:
            if v not in lost:
                lost.add(v);q.append(v)
    keep={v:p for v,p in c.parent.items() if v not in lost}
    parent=keep|{v:None for v in new.roots if v not in keep}
    todo=deque(sorted(parent.keys()-keep.keys()))

    def seed(v,u):
        if v not in parent:
            parent[v]=u;todo.append(v)
    for v in sorted(lost):
        if v not in parent:
            for u in sorted(new.rev[v]):
                if u in keep:
                    seed(v,u);break
    for u in e.out.keys() & keep.keys():
        for v in sorted(new.out[u]-old.out[u]):
            seed(v,u)
    reads=0
    while todo:
        u=todo.popleft();reads+=1
        for v in sorted(new.out[u]):seed(v,u)
    removed=(c.parent.keys()-parent.keys()) | (e.facts.keys() & c.parent.keys())
    added=(parent.keys()-c.parent.keys()) | (e.facts.keys() & parent.keys())
    d=Cache(parent,deepcopy(c.bad),deepcopy(c.views),set(c.conflicts))
    for k in removed:
        change_fact(d,k,old.facts[k],False)
    for k in added:
        change_fact(d,k,new.facts[k],True)
    work=dict(out_reads=len(e.out)+reads,reverse_reads=len(lost),
              fact_reads=len(removed)+len(added),tree_vertices_indexed=len(c.parent),
              retained=len(keep),repaired=len(parent)-len(keep))
    return new,d,work
