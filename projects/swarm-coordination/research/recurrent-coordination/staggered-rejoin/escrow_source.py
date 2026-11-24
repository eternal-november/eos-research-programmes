"""Trusted documentary evidence for a simulated warehouse; no cryptographic API."""
from dataclasses import dataclass
from itertools import combinations, permutations
from collections import Counter
import json

@dataclass(frozen=True, order=True)
class ID:
    issuer: str
    n: int

@dataclass(frozen=True)
class Grant:
    id: ID
    right: str
    lineage: tuple
    cumulative: tuple

@dataclass(frozen=True)
class Receipt:
    id: ID

@dataclass(frozen=True)
class Handoff:
    right: str
    generation: int
    owner: str
    receiver: str
    prior: tuple

def require(condition):
    if not condition:
        raise ValueError("transition not enabled")

def prefix(ids,i):
    f=0
    while ID(i,f+1) in ids:
        f+=1
    return f

def high(ids):
    p={}
    for j in ids:
        p[j.issuer]=max(p.get(j.issuer,0),j.n)
    return tuple(sorted(p.items()))

def expand(vector):
    return {ID(i,j) for i,f in vector for j in range(1,f+1)}

def unpack(d):
    return sorted((i,u) for i,u in d.items() if u)

class Warehouse:
    """Instrumented transitions; policy uses issuer-local rights and learned receipts."""
    def __init__(self,owners):
        self.owners=dict(owners)
        self.generation=Counter()
        self.wire={}
        self.chain={r:[] for r in owners}
        self.grants={}
        self.issued=Counter()
        self.learned={i:set() for i in "ABCX"}
        self.locals={i:{r:() for r,owner in owners.items() if owner==i} for i in "ABCX"}
        self.running={}
        self.authentic={}
        self.acc={i:set() for i in "ABCX"}
        self.trace=[]

    def learn(self,issuer,receipt):
        require(self.authentic.get(receipt.id) is receipt)
        self.learned[issuer].add(receipt.id)
        self.trace.append(('receipt_at_issuer',issuer,receipt.id.issuer,receipt.id.n))

    def ready(self,owner,r):
        return all(prefix(self.learned[owner],i)>=f for i,f in self.locals[owner][r])

    def issue(self,i,r):
        require(r in self.locals[i] and self.ready(i,r))
        assert r not in self.running
        self.issued[i]+=1
        j=ID(i,self.issued[i])
        lineage=self.locals[i][r]
        self.acc[i].update(expand(lineage))
        g=Grant(j,r,lineage,high(self.acc[i]))
        self.chain[r].append(j)
        self.locals[i][r]=high(expand(lineage)|{j})
        self.grants[j]=g
        self.running[r]=j
        self.trace.append(('issue',i,j.n,r))
        return g

    def settle(self,g):
        require(self.grants.get(g.id) is g and self.running.get(g.right)==g.id)
        del self.running[g.right]  # physically release only after receiving rack accepts
        receipt=Receipt(g.id)
        self.authentic[g.id]=receipt
        self.trace.append(('rack_accepts',g.id.issuer,g.id.n,g.right))
        return receipt

    def send_right(self,owner,receiver,r):
        require(r in self.locals[owner] and r not in self.wire)
        prior=self.locals[owner].pop(r)
        self.generation[r]+=1
        h=Handoff(r,self.generation[r],owner,receiver,prior)
        self.wire[r]=h
        self.trace.append(('send_right',r,h.generation,owner,receiver))
        return h

    def receive_right(self,receiver,h):
        require(self.wire.get(h.right) is h and h.receiver==receiver)
        del self.wire[h.right]
        require(h.right not in self.locals[receiver])
        self.locals[receiver][h.right]=h.prior
        self.trace.append(('receive_right',h.right,h.generation,receiver))

    def invariant(self):
        for r in self.owners:
            assert int(r in self.wire)+sum(r in rs for rs in self.locals.values())==1
            resident=[rs[r] for rs in self.locals.values() if r in rs]
            actual=self.wire[r].prior if r in self.wire else resident[0]
            assert actual==high(self.chain[r])
        assert len(set(self.running.values()))==len(self.running)
        assert set(self.running.values())|set(self.authentic)==set(self.grants)
        assert set(self.running.values()).isdisjoint(self.authentic)

class View:
    def __init__(self):
        self.U={}
        self.F={}
        self.tail=set()
    @property
    def S(self):
        return expand(self.F.items()) | self.tail
    def normalized(self):
        self.tail={j for j in self.tail if self.F.get(j.issuer,0)<j.n}
        for i in self.U:
            while ID(i,self.F.get(i,0)+1) in self.tail:
                self.F[i]=self.F.get(i,0)+1
                self.tail.remove(ID(i,self.F[i]))
        assert not any(j.n>self.U[j.issuer] for j in self.tail)
    def query(self,j):
        if j.n>self.U.get(j.issuer,0): return 'unknown'
        return 'settled' if j.n<=self.F.get(j.issuer,0) or j in self.tail else 'awaiting'
    def learn_prefix(self,vec):
        for i,n in vec:
            self.U[i]=max(self.U.get(i,0),n)
            self.F[i]=max(self.F.get(i,0),n)
        self.normalized()
    def grant(self,plant,g,mode):
        require(plant.grants.get(g.id) is g)
        cert = g.cumulative if mode=='bundled' else g.lineage if mode=='lineage' else ()
        self.learn_prefix(cert)
        self.U[g.id.issuer]=max(self.U.get(g.id.issuer,0),g.id.n)
    def receipt(self,plant,r,bare=False):
        require(plant.authentic.get(r.id) is r)
        if r.id.n>self.U.get(r.id.issuer,0) and not bare:
            return False
        self.U[r.id.issuer]=max(self.U.get(r.id.issuer,0),r.id.n)
        self.tail.add(r.id)
        self.normalized()
        return True
    def join(self,v):
        w=View()
        for i in self.U.keys()|v.U.keys():
            w.U[i]=max(self.U.get(i,0),v.U.get(i,0))
            w.F[i]=max(self.F.get(i,0),v.F.get(i,0))
        w.tail=self.tail|v.tail
        w.normalized()
        return w
    def width(self):
        return sum(n-self.F.get(i,0) for i,n in self.U.items())
    def report(self):
        return dict(U=unpack(self.U), settled=sorted((j.issuer,j.n) for j in self.S), width=self.width())

def deny(f):
    try: f()
    except ValueError: return
    raise AssertionError('expected refusal')

def multiauthority():
    p=Warehouse({'p':'X','q':'A'})
    x=p.issue('X','p')
    deny(lambda:p.issue('X','p'))
    h=p.send_right('X','A','p')
    deny(lambda:p.issue('X','p'))
    deny(lambda:p.issue('A','p'))
    p.receive_right('A',h)
    deny(lambda:p.receive_right('A',h))
    deny(lambda:p.issue('A','p'))
    rx=p.settle(x)
    deny(lambda:p.issue('A','p'))  # physical release, but not learned
    deny(lambda:p.learn('A',Receipt(x.id)))
    p.learn('A',rx)
    a1=p.issue('A','p')
    a2=p.issue('A','q')
    ra2=p.settle(a2)
    p.learn('A',ra2)
    deny(lambda:p.issue('A','q'))  # an old A:1 hole blocks a physically free right
    p.invariant()
    return p,x,a1,a2,rx,ra2

def chains():
    p=Warehouse({'p':'A'})
    obs=[]
    prev=None
    for i in 'ABC':
        if prev is not None:
            p.receive_right(i,p.send_right(prev,i,'p'))
            # In this envelope prior prefix receipts are delivered to the new owner.
            for rr in tuple(p.authentic.values()): p.learn(i,rr)
        g=p.issue(i,'p')
        p.settle(g)
        obs.append(g)
        prev=i
    p.invariant()
    return p,obs

def subset(seq):
    for n in range(len(seq)+1):
        yield from combinations(seq,n)

def split(p,gs,rs=()):
    n=0
    for L in subset(gs):
        for R in subset(gs):
            a,b=View(),View()
            for g in L: a.grant(p,g,'bundled')
            for g in R: b.grant(p,g,'bundled')
            for s in rs:
                a.receipt(p,s)
                b.receipt(p,s)
            c=a.join(b)
            expected=set().union(*(expand(g.cumulative) for g in set(L)|set(R)))
            for r in rs:
                if r.id.n<=a.U.get(r.id.issuer,0) or r.id.n<=b.U.get(r.id.issuer,0):
                    expected.add(r.id)
            assert c.S==expected and c.width()<=len(p.owners)
            assert c.report()==b.join(a).report()==c.join(a).report()
            for i,u in c.U.items():
                for j in range(1,u+1):
                    assert c.query(ID(i,j))==('settled' if ID(i,j) in expected else 'awaiting')
                assert c.query(ID(i,u+1))=='unknown' 
            n+=1
    return n

def causal_orders(p,gs):
    """A seal models a genuine grant-plus-dependencies from the same source."""
    schedule=tuple((g,kind) for g in gs for kind in ('header','proof'))
    n=0
    pending_peak=0
    for sequence in permutations(schedule):
        open_parts={g:set() for g in gs}
        bundle, direct=View(),View()
        for g,kind in sequence:
            open_parts[g].add(kind)
            if len(open_parts[g])==2:
                bundle.grant(p,g,'bundled')
                direct.learn_prefix(g.cumulative)
                direct.grant(p,g,'bare')
            assert bundle.report()==direct.report() and direct.width()<=len(p.owners)
            pending_peak=max(pending_peak,sum(len(q)==1 for q in open_parts.values()))
            n+=1
    return dict(cuts=n, peak_unpaired_parts=pending_peak, bundled_units=len(gs),
                separate_units=2*len(gs), certified_prefix_entries=sum(len(g.cumulative) for g in gs))


def repeated(n):
    p=Warehouse({'p':'A','q':'B'})
    previous=View()
    totals=Counter()
    for k in range(n):
        active='A' if k%2==0 else 'B'
        other='B' if active=='A' else 'A'
        first=p.issue(active,'p')
        second=p.issue(other,'q')
        left,right=View(),View()
        right.grant(p,second,'bundled')
        receipt=p.settle(second)
        p.learn(other,receipt)
        assert right.receipt(p,receipt)
        left.grant(p,first,'bundled')
        current=left.join(right).join(previous)
        assert current.width()<=2
        assert current.query(first.id)=='awaiting'
        assert current.query(second.id)=='settled'
        late=p.settle(first)
        p.learn(active,late); p.learn(other,late)
        left.receipt(p,late)
        previous=left.join(current)
        p.receive_right(other,p.send_right(active,other,'p'))
        p.receive_right(active,p.send_right(other,active,'q'))
        # Give each post-handoff issuer the next relevant prior prefixes.
        p.learn(active,receipt)
        p.invariant()
        totals['issues']+=2
        totals['splits_rejoins']+=1
        totals['authority_handoffs']+=2
    return dict(totals, final_U=unpack(previous.U), final_F=unpack(previous.F), final_width=previous.width())

def run():
    p,x,a1,a2,rx,ra2=multiauthority()
    a,b=View(),View()
    a.grant(p,x,'bundled'); b.grant(p,a2,'bundled')
    full=a.join(b)
    un=View()
    for g in (x,a2): un.grant(p,g,'lineage')
    assert full.width()==2 and un.width()==3
    bare=View()
    bare.grant(p,x,'bundled')
    assert not bare.receipt(p,ra2)
    assert bare.receipt(p,ra2,True) and bare.width()==3
    atomic=View()
    atomic.grant(p,x,'bundled')
    atomic.grant(p,a2,'bundled')
    assert atomic.receipt(p,ra2) and atomic.width()==2
    direct=View()
    # Separate causal message arrives first. Until then A:2 is buffered.
    direct.grant(p,x,'bare')
    direct.learn_prefix(a2.cumulative)
    assert direct.width()<=2
    direct.grant(p,a2,'bare')
    assert direct.report()==full.report()
    direct.receipt(p,ra2)
    assert direct.report()==atomic.report()
    c, (ga,gb,gc)=chains()
    weak,strong=View(),View()
    for g in (ga,gc):
        weak.grant(c,g,'bare')
        if g is gc: weak.learn_prefix(((gb.id.issuer,gb.id.n),))
        strong.grant(c,g,'bundled')
    assert weak.width()==2 and strong.width()==1
    # Fixed rights demand replay at A after a settled X job: A may use its
    # one q but cannot absorb the freed p to have two live jobs.
    fixed=Warehouse({'p':'X','q':'A'})
    x0=fixed.issue('X','p'); fixed.settle(x0)
    fixed.issue('A','q')
    deny(lambda:fixed.issue('A','p'))
    fixed.invariant()
    # Clear A:1 eventually; q can start only after both receipts are known.
    ra1=p.settle(a1); p.learn('A',ra1)
    assert p.issue('A','q').id==ID('A',3)
    p.invariant()
    return dict(
        joined_views=split(p,(x,a1,a2),(rx,ra2))+split(c,(ga,gb,gc)),
        full=full.report(), no_cumulative=un.report(), bare_receipt=bare.report(),
        atomic_receipt=atomic.report(), immediate_predecessor=weak.report(),
        full_transitive=strong.report(),
        prefix_entry_cost=dict(bundled=[len(g.cumulative) for g in (x,a1,a2,ga,gb,gc)],
                               separate_causal=[len(g.cumulative) for g in (x,a1,a2,ga,gb,gc)]),
        warehouse_trace=p.trace, lineage_trace=c.trace, fixed_trace=fixed.trace,
        recurrent=repeated(50), atomic_causal_publication=causal_orders(p,(x,a1,a2)))

if __name__=='__main__':
    print(json.dumps(run(),indent=1,sort_keys=True))
