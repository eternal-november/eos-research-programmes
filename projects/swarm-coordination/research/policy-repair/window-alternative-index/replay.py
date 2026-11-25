"""Incrementally maintain scope-checked proof alternatives, including absent keys."""
from dataclasses import dataclass
from collections import Counter, OrderedDict
from pathlib import Path
from itertools import product
from random import Random
import json,sys

@dataclass
class Node:
    k:tuple
    h:int=1
    left:object=None
    right:object=None

def height(t):return t.h if t else 0
def refresh(t):
    t.h=1+max(height(t.left),height(t.right));return t
def left(t):
    u=t.right;t.right=u.left;u.left=refresh(t);return refresh(u)
def right(t):
    u=t.left;t.left=u.right;u.right=refresh(t);return refresh(u)
def balance(t,c):
    refresh(t)
    if height(t.left)-height(t.right)>1:
        if height(t.left.left)<height(t.left.right):t.left=left(t.left);c['rotations']+=1
        c['rotations']+=1
        return right(t)
    if height(t.right)-height(t.left)>1:
        if height(t.right.right)<height(t.right.left):t.right=right(t.right);c['rotations']+=1
        c['rotations']+=1
        return left(t)
    return t
def insert(t,k,c):
    c['watch_writes']+=1
    if t is None:return Node(k)
    assert k!=t.k
    if k<t.k:t.left=insert(t.left,k,c)
    else:t.right=insert(t.right,k,c)
    return balance(t,c)
def remove(t,k,c):
    assert t
    c['watch_writes']+=1
    if k<t.k:t.left=remove(t.left,k,c)
    elif k>t.k:t.right=remove(t.right,k,c)
    elif not t.left or not t.right:return t.left or t.right
    else:
        u=t.right
        while u.left:u=u.left;c['watch_writes']+=1
        t.k=u.k;t.right=remove(t.right,u.k,c)
    return balance(t,c)
def report(t,lo,hi,c):
    if not t:return
    c['range_visits']+=1
    d,i=t.k
    if d>=lo:yield from report(t.left,lo,hi,c)
    if lo<=d<=hi:yield i
    if d<=hi:yield from report(t.right,lo,hi,c)

def check_tree(t,lo=None,hi=None):
    if not t:return (0,set())
    assert (lo is None or t.k>lo) and (hi is None or t.k<hi)
    ha,sa=check_tree(t.left,lo,t.k);hb,sb=check_tree(t.right,t.k,hi)
    assert t.h==1+max(ha,hb) and abs(ha-hb)<=1
    return t.h,sa|sb|{t.k}

def inside(w,d):return w is not None and w[0]<=d<=w[1]
def difference(a,b):
    if a is None:return []
    if b is None:return [a]
    lo,hi=a;bl,bh=b
    return [(x,y) for x,y in ((lo,min(hi,bl-1)),(max(lo,bh+1),hi)) if x<=y]

class Watch:
    def __init__(self,deadlines):
        self.deadlines=deadlines
        self.sources={}
        self.edges={i:set() for i in range(len(deadlines))}
        self.index={};self.good={i:OrderedDict() for i in self.edges}
        self.cost=Counter()
    def window(self,k):return self.sources.get(k,(0,None,None))[2]
    def set_cell(self,i,k,ok):
        if ok:self.good[i][k]=None
        else:del self.good[i][k]
        self.cost['atom_flips']+=1
    def add(self,i,k):
        assert k not in self.edges[i]
        self.edges[i].add(k)
        d=self.deadlines[i]
        self.index[k]=insert(self.index.get(k),(d,i),self.cost)
        self.cost['cold_reads']+=1
        if inside(self.window(k),d):self.set_cell(i,k,True)
    def delete(self,i,k):
        self.edges[i].remove(k)
        self.index[k]=remove(self.index[k],(self.deadlines[i],i),self.cost)
        if k in self.good[i]:self.set_cell(i,k,False)
    def update(self,k,version,provider,w):
        old=self.sources.get(k,(0,None,None))
        if version<=old[0]:
            self.cost['rejected_epoch']+=1
            return
        self.cost['source_records']+=1
        self.sources[k]=version,provider,w
        if old[2]==w:return
        for a,b,ok in [(old[2],w,False),(w,old[2],True)]:
            for lo,hi in difference(a,b):
                for i in report(self.index.get(k),lo,hi,self.cost):
                    self.set_cell(i,k,ok)
    def choose(self,i):
        self.cost['queries']+=1
        k=next(iter(self.good[i]),None)
        if k is not None:
            self.cost['proof_fetches']+=1
            row=self.sources[k]
            assert inside(row[2],self.deadlines[i])
            return k,row[0],row[1]
    def validates(self,i,ticket):
        if ticket is None:return not self.good[i]
        k,e,provider=ticket
        return (k in self.edges[i] and self.sources[k][:2]==(e,provider)
                and inside(self.window(k),self.deadlines[i]))

class Scan(Watch):
    def __init__(self,d):
        super().__init__(d);self.inverse={}
    def add(self,i,k):
        self.edges[i].add(k);self.inverse.setdefault(k,set()).add(i)
        self.cost['watch_writes']+=1;self.cost['cold_reads']+=1
        if inside(self.window(k),self.deadlines[i]):self.set_cell(i,k,True)
    def delete(self,i,k):
        self.edges[i].remove(k);self.inverse[k].remove(i);self.cost['watch_writes']+=1
        if k in self.good[i]:self.set_cell(i,k,False)
    def update(self,k,version,provider,w):
        old=self.sources.get(k,(0,None,None))
        if version<=old[0]:self.cost['rejected_epoch']+=1;return
        self.sources[k]=version,provider,w
        self.cost['source_records']+=1
        if old[2]==w:return
        for i in self.inverse.get(k,()):
            self.cost['incident_visits']+=1
            was=k in self.good[i];now=inside(w,self.deadlines[i])
            if was!=now:self.set_cell(i,k,now)

def paths(n,triples):
    d=tuple(range(n));a,b=Watch(d),Scan(d)
    def audit():
        assert a.edges==b.edges and a.sources==b.sources
        for i,ks in a.edges.items():
            expected={k for k in ks if inside(a.window(k),d[i])}
            assert expected==set(a.good[i])==set(b.good[i])
        for k in a.index:
            t,mem=check_tree(a.index[k])
            assert mem=={(d[i],i) for i in b.inverse[k]}
    def both(name,*args):
        for o in a,b:getattr(o,name)(*args)
    for name,args in triples:both(name,*args)
    audit()
    return a,b

def verify():
    rng=Random(428);controls=0
    # All interval symmetric differences on a small domain.
    ints=[None]+[(a,b) for a in range(7) for b in range(a,7)]
    for a,b,d in product(ints,ints,range(7)):
        assert any(inside(w,d) for w in difference(a,b))==(inside(a,d) and not inside(b,d))
        controls+=1
    # Subscribed absent key is essential; after two overlapping appointments
    # one still-pending receiver is redirected and must never use its old ticket.
    base=[('add',(0,'A')),('add',(0,'B')),('update',('A',1,'initial',(0,5)))]
    a,b=paths(5,base)
    old=a.choose(0);assert old==('A',1,'initial')
    for o in a,b:
        o.update('B',1,'successor',(0,5))
        o.delete(0,'A')
        o.update('A',2,'renewed',(0,5))
        assert not o.validates(0,old)
        assert o.choose(0)==('B',1,'successor')
        o.update('B',2,'substitute',(0,5))
        o.update('B',1,'stale',None)
        assert not o.validates(0,('B',1,'successor'))
        assert o.choose(0)==('B',2,'substitute')
    small=0; edit_a=Counter(); edit_b=Counter()
    for _ in range(18):
        obs=[(rng.randrange(14),chr(65+rng.randrange(4))) for _ in range(90)]
        ed=set();cmd=[]
        for j,(i,k) in enumerate(obs,1):
            act='delete' if (i,k) in ed else 'add'
            if act=='add':ed.add((i,k))
            else:ed.remove((i,k))
            cmd.append((act,(i,k)))
            lo,hi=sorted((rng.randrange(15),rng.randrange(15)))
            cmd.append(('update',(k,j,f'p{j}',None if j%5==0 else (lo,hi))))
            # A slow audit across every dynamic-prefix mutation.
            if j%7==0:paths(14,cmd);small+=1
        ra,rb=paths(14,cmd)
        edit_a.update(ra.cost);edit_b.update(rb.cost)
    n=4096
    initial=[('add',(i,'heavy')) for i in range(n)]
    changes=[('update',('heavy',1,'p0',(0,n-1)))]
    # Exclude cold-start common work in the cumulative update comparison.
    a,b=paths(n,initial+changes)
    warm_a,warm_b=dict(a.cost),dict(b.cost)
    for o in (a,b):o.cost.clear()
    for v in range(2,130):
        w=(v%2,n-1)
        a.update('heavy',v,f'p{v}',w);b.update('heavy',v,f'p{v}',w)
    assert all(set(a.good[i])==set(b.good[i]) for i in range(n))
    ac,bc=dict(a.cost),dict(b.cost)
    assert ac.get('range_visits',0)<bc['incident_visits']/100
    assert ac['atom_flips']==bc['atom_flips']==127
    return dict(exact_interval_checks=controls,independent_prefix_audits=small,
        family={'subscribers':n,'updates':128,'indexed':ac,'factored_scan':bc,
            'cold_indexed':warm_a,'cold_scan':warm_b},
        dynamic_allocations={'indexed':dict(edit_a),'factored_scan':dict(edit_b)},
        role_change_witness='B serves old duty without receiver rewrite; superseded epoch cannot settle it')

if __name__=='__main__':
    output=json.dumps(verify(),sort_keys=True,indent=2)+'\n'
    if len(sys.argv)>1:Path(sys.argv[1]).write_text(output)
    else:print(output,end='')
