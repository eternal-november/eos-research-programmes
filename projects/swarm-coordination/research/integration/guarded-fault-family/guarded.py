"""Finite guarded DAG; each path must keep one fixed law assignment."""
from functools import lru_cache
import heapq

class BDD:
    def __init__(self):self.nodes=[None,None];self.cache={}
    def node(self,v,a,b):
        if a==b:return a
        k=(v,a,b)
        if k not in self.cache:
            self.cache[k]=len(self.nodes);self.nodes.append(k)
        return self.cache[k]
    def atom(self,v):return self.node(v,0,1)
    @lru_cache(None)
    def op(self,kind,a,b):
        if b<a:return self.op(kind,b,a)
        if kind=='and':
            if a==0:return 0
            if a==1 or a==b:return b
        else:
            if a==0:return b
            if a==1:return 1
            if a==b:return a
        av,al,ah=self.nodes[a];bv,bl,bh=self.nodes[b]
        v=min(av,bv)
        p,q=(al,ah) if v==av else (a,a)
        r,s=(bl,bh) if v==bv else (b,b)
        return self.node(v,self.op(kind,p,r),self.op(kind,q,s))
    @lru_cache(None)
    def neg(self,i):
        if i<2:return 1-i
        v,a,b=self.nodes[i]
        return self.node(v,self.neg(a),self.neg(b))
    def val(self,i,assignment):
        while i>1:
            v,a,b=self.nodes[i];i=b if assignment[v] else a
        return bool(i)
    def sat(self,i):
        assert i!=0
        a={}
        while i>1:
            v,l,h=self.nodes[i]
            a[v]=not bool(l)
            i=l if l else h
        return a

class Family:
    def __init__(self,B,roots,n,edges,bad):
        self.b=B;self.roots=frozenset(roots);self.bad=frozenset(bad)
        self.edge=dict(edges);self.incoming=[[] for _ in range(n)]
        self.outgoing=[[] for _ in range(n)]
        self.reach=[0]*n
        for name,(u,v,_) in self.edge.items():
            assert 0<=u<v<n
            self.incoming[v].append(name);self.outgoing[u].append(name)
        for v in range(n):self.reach[v]=self._row(v)
    def _row(self,v):
        val=int(v in self.roots)
        for name in self.incoming[v]:
            u,_,g=self.edge[name]
            val=self.b.op('or',val,self.b.op('and',self.reach[u],g))
        return val
    def replace_guards(self,changes):
        dirty=set()
        for name,g in changes.items():
            u,v,old=self.edge[name]
            if old!=g:
                self.edge[name]=(u,v,g);dirty.add(v)
        pending=list(dirty);heapq.heapify(pending);read=0
        while pending:
            v=heapq.heappop(pending);dirty.remove(v)
            r=self._row(v);read+=1
            if r==self.reach[v]:continue
            self.reach[v]=r
            for name in self.outgoing[v]:
                _,w,_=self.edge[name]
                if w not in dirty:
                    dirty.add(w);heapq.heappush(pending,w)
        return read
    def violation(self):
        val=0
        for v in sorted(self.bad):val=self.b.op('or',val,self.reach[v])
        return val
    def witness(self,assign):
        v=next(v for v in sorted(self.bad) if self.b.val(self.reach[v],assign))
        path=[]
        while v not in self.roots:
            name=next(n for n in self.incoming[v]
                        if self.b.val(self.edge[n][2],assign)
                        and self.b.val(self.reach[self.edge[n][0]],assign))
            path.append(name);v=self.edge[name][0]
        return tuple(reversed(path))
