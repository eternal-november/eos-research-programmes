"""Civil synthetic receiver; legacy commands and motion are abstract events."""
from dataclasses import dataclass
from itertools import product
from receiver import Fact, Job, Key, Kind, choose

@dataclass
class Receiver:
    # Fresh generation per model, unbounded counters here.
    lo: int=0
    base: int=1
    accepted: int=0
    def receive(self, version, stitch, end):
        if version < self.lo or version <= self.accepted or stitch != self.base:
            return False
        self.accepted=version
        assert end>=stitch
        self.base=end
        return True
    def seal(self, bound):
        # One receiver event, not two messages.
        self.lo=max(self.lo,bound)
        return self.lo,self.base

def model(delivery,seal,arrive,clear,grant,protect,deadline,order,stock_wait, end):
    obj=Receiver()
    if delivery<seal or (delivery==seal and order=="before"):
        obj.receive(1,1,end)
    floor,observed=obj.seal(2)
    cut_base=obj.base
    if delivery>seal or (delivery==seal and order=="after"):
        obj.receive(1,1,end)
    assert floor==2 and obj.base==cut_base
    # Old generation may still move along its admitted prefix. Protect only a
    # specified footprint whose first possible conflict is old step 2.
    start=max(seal+arrive,clear,grant)
    nonce="new inspection: bay A"
    f,q,g=(Key(k,"bay A","legacy generation",nonce)
           for k in (Kind.FENCED,Kind.QUIESCENT,Kind.GRANTED))
    upper=max(deadline+1,start+protect+1)
    facts=[Fact(q,clear,clear,upper),Fact(g,grant,grant,upper)]
    if observed<2:
        facts.append(Fact(f,seal+arrive,seal,upper))
    admitted=choose(Job(frozenset({f,q,g}),0,deadline,protect), start, facts)
    admission=admitted is not None
    assert admitted in (None,start)
    # Without a receiver seal, only settled publication status or a later
    # physically verified fallback can make protection available.
    stock_start=max(stock_wait,clear,grant)
    stock=stock_start+protect<=deadline
    return admission,stock,start

def exhaustive():
    n=plus=tie=0
    for d,s,a,q,g,p,D,o,r,e in product(range(4),range(4),range(3),range(4),range(4),
                                     (1,2),range(1,8),("before","after"),range(4,8),(1,2,3)):
        yes,no,start=model(d,s,a,q,g,p,D,o,r,e)
        # Direct temporal test model: was the pre-cut step forced into the
        # accepted prefix? Is the entrant in the protected interval only
        # after permission and clearance and before its deadline?
        accepted=((d,0 if o=="before" else 2)<(s,1)) and e>=2
        direct=not accepted and any(t>=s+a and t>=q and t>=g and t+p<=D for t in range(D+1))
        assert yes==direct
        assert no==(any(t>=r and t>=q and t>=g and t+p<=D for t in range(D+1)))
        n+=1
        plus+=yes and not no
        tie+=yes==no
    print("exact comparisons",n,"seal-only successes",plus,"equal",tie)
    assert model(3,1,1,2,2,2,4,"after",5,2)==(True,False,2)
    assert model(1,1,1,2,2,2,4,"before",5,2)==(False,False,2)
    assert model(3,1,1,3,2,2,4,"after",5,2)==(False,False,3)
    # Reading a snapshot at 1 does not stop a release at 3.
    r=Receiver()
    assert r.base==1 and r.receive(1,1,2)
    print("launch 2, finish 4; fails if accepted first or clearance at 3")

if __name__=="__main__":
    exhaustive()
