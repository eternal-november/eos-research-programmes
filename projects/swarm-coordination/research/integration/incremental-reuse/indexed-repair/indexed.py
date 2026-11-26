"""Incremental single-installation graph store with rooted witness repair."""
from collections import defaultdict, deque
from reuse import Cache,Graph,change_fact,full

class Indexed:
    def __init__(self,g):
        self.out=dict(g.out)
        self.rev={v:set(ps) for v,ps in g.rev.items()}
        self.roots=g.roots
        self.facts=dict(g.facts)
        self.cache,_=full(g)
        self.children=defaultdict(set)
        for v,p in self.cache.parent.items():
            if p is not None:self.children[p].add(v)

    def update(self,e):
        C=self.cache
        exist=self.out.keys()
        assert all(u in exist and all(v in exist for v in vs)
                   for u,vs in e.out.items()) and e.facts.keys()<=exist
        assert e.roots is None or e.roots<=exist
        metrics=dict(edits=len(e.out),out_rows_read=0,diff_members=0,
                     reverse_members_read=0,child_links_read=0,root_items_read=0,
                     invalidated=0,reconnected=0,fact_updates=0)
        metrics['diff_members']=sum(len(vs) for vs in e.out.values())
        for k in e.facts:
            if k in C.parent:
                change_fact(C,k,self.facts[k],False)
                metrics['fact_updates']+=1
        self.facts.update(e.facts)
        detached_roots=set()
        new_roots=set()
        if e.roots is not None:
            metrics['root_items_read']=len(self.roots)+len(e.roots)
            new_roots=e.roots-self.roots
            detached_roots.update(v for v in self.roots-e.roots if C.parent[v] is None)
            self.roots=e.roots
        gained={}
        for u,row in e.out.items():
            before=self.out[u];metrics['out_rows_read']+=1
            metrics['diff_members']+=len(before)
            for v in before-row:
                self.rev[v].remove(u)
                if C.parent.get(v)==u:detached_roots.add(v)
            gained[u]=row-before
            for v in gained[u]:self.rev[v].add(u)
            self.out[u]=row
        lost=set(detached_roots)
        stack=list(lost)
        while stack:
            u=stack.pop()
            for v in self.children.get(u,()):
                metrics['child_links_read']+=1
                if v not in lost:
                    lost.add(v);stack.append(v)
        for v in lost:
            p=C.parent.pop(v)
            if p is not None and p not in lost:self.children[p].remove(v)
            self.children.pop(v,None)
        metrics['invalidated']=len(lost)
        queue=deque()
        fresh=set()
        def seed(v,p):
            if v not in C.parent:
                C.parent[v]=p
                if p is not None:self.children[p].add(v)
                queue.append(v)
                if v not in lost:fresh.add(v)
        for v in sorted(new_roots|{v for v in lost if v in self.roots}):
            seed(v,None)
        for v in sorted(lost):
            if v not in C.parent:
                preds=self.rev[v]
                # Count all inspected entries, including the stable-order
                # traversal used to choose a reproducible witness.
                metrics['reverse_members_read']+=len(preds)
                for u in sorted(preds):
                    if u in C.parent:
                        seed(v,u);break
        for u,children in gained.items():
            if u in C.parent:
                for v in sorted(children):seed(v,u)
        while queue:
            u=queue.popleft()
            metrics['out_rows_read']+=1
            for v in sorted(self.out[u]):seed(v,u)
        for v in lost:
            if v in C.parent:metrics['reconnected']+=1
            elif v not in e.facts:
                change_fact(C,v,self.facts[v],False)
                metrics['fact_updates']+=1
        for v in fresh|{v for v in e.facts if v in C.parent}:
            change_fact(C,v,self.facts[v],True)
            metrics['fact_updates']+=1
        return metrics

    def snapshot(self):
        """Explicit full snapshot for export/oracle, not needed by update."""
        return Graph(self.roots,dict(self.out),dict(self.facts))
