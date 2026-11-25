"""Scoped source watermarks with physically enforced mutation fences."""
from dataclasses import dataclass
from collections import defaultdict
from footprint import Plant

@dataclass(frozen=True)
class Receipt:
    helper:int
    epoch:int
    role:int
    delta:int

@dataclass(frozen=True)
class Ticket:
    helper:int
    epoch:int
    locked_from:int
    locked_until:int

class FieldPlant(Plant):
    def __init__(self,R):
        super().__init__(R)
        self.epochs=defaultdict(int)
        self.ticket=defaultdict(int)

    def close_scope(self,h,now,until):
        assert now<until
        self.ticket[h]=max(self.ticket[h],until)
        return Ticket(h,self.epochs[h],now,until)

    def _row(self,h,j,d):
        self.epochs[h]+=1
        return Receipt(h,self.epochs[h],j,d)

    def support(self,j,at,physical_ready):
        q=self.R[j];candidate=q.prepare_to
        assert candidate is not None
        # A candidate may approach, but if the actual new helper is
        # physically fenced the final commit tick is not admitted. The
        # current helper's outstanding predecessor remains a relation.
        locked=at<self.ticket[candidate]
        row=super().support_tick(j,physical_ready and not locked)
        if row is None:return None
        _,op,j,token,old,new=row
        assert op=="mate"
        return self._row(new,j,1)

    def retire(self,j,token,at,verified_clear):
        q=self.R[j]
        if token not in q.tail or not verified_clear:return None
        r=q.tail[token]
        # A fence also ties certification of a retiring membership to
        # the reservation. Physical finish may occur; release of its
        # conservative tracked dependence is deferred until this scope
        # is no longer used in a live certificate.
        if at<self.ticket[r]:return None
        A=super().actual_settle(j,token,True)
        assert A and A[4]==r
        return self._row(r,j,-1)

class LocalCheck:
    def __init__(self,R):
        self.index=defaultdict(dict)
        self.epoch=defaultdict(int)
        self.nwrite=0
        for j,h in enumerate(R):self.index[h][j]=1

    def deliver(self,row):
        h,q,j,d=row.helper,row.epoch,row.role,row.delta
        if q!=self.epoch[h]+1:return False
        z=self.index[h].get(j,0)+d
        assert z>=0
        if z:self.index[h][j]=z
        else:del self.index[h][j]
        self.epoch[h]=q;self.nwrite+=1
        return True

    def consume(self,h,t0,t1,ticket):
        if (ticket is None or ticket.helper!=h or
              not(ticket.locked_from<=t0<t1<=ticket.locked_until) or
              ticket.epoch!=self.epoch[h]):
            return None
        return set(self.index[h])

def not_required_by(roles,reading):
    # Absence of these dependencies is not physical availability.
    # The predicate applies to a source-side fence with a
    # receipt and current membership stream.
    return reading is not None and not (set(roles)&reading)

def derived_field():
    P=FieldPlant([0,2]);V=LocalCheck([0,2])
    P.prepare(0,1)
    assert P.support(0,0,True) is None
    lost=P.support(0,1,True)
    # A certified handoff actually added role 0 to helper 1. The
    # migration receipt has not arrived but the local epoch marker did.
    ticket1=P.close_scope(1,2,6)
    assert V.consume(1,2,5,ticket1) is None
    assert V.consume(1,2,5,None) is None
    # Independent local scope remains verifiable; no global "quiet".
    good=P.close_scope(2,2,5)
    assert V.consume(2,2,5,good)=={1}
    assert V.deliver(lost)
    assert V.consume(1,2,5,ticket1)=={0}
    assert not not_required_by({0},V.consume(1,2,5,ticket1))
    assert not V.deliver(lost)
    # No global freeze: another support move to a different helper
    # succeeds while the bounded local commitments are certified.
    P.prepare(1,4)
    assert P.support(1,2,True) is None
    assert V.deliver(P.support(1,3,True))
    assert V.consume(2,3,5,good)=={1} # actual retained predecessor
    assert P.retire(1,2,4,True) is None
    assert V.deliver(P.retire(1,2,5,True))
    assert V.consume(2,5,6,good) is None
    # A dropped receipt for a new slot must not affect proven other slots.
    # Fencing has a real workload cost: a new entrant cannot start its
    # two required support ticks on that helper within this source model.
    P.prepare(0,2)
    sheltered=P.close_scope(2,6,8)
    assert P.support(0,6,True) is None and P.support(0,7,True) is None
    assert P.support(0,8,True) is None and P.support(0,9,True) is not None
    assert V.consume(2,7,8,sheltered)==set()
    print("the selected source fence delays a new physical move by two ticks") 
    print("only the changed helper waits for the missing migration event")
    print("another role changes producer and still holds its earlier duty under a scoped fence")

def tests():
    from random import Random
    rng=Random(5565);N=50
    R=[rng.randrange(12) for _ in range(N)];P=FieldPlant(R);V=LocalCheck(R)
    pending=[];count=updates=blocked=0
    for t in range(3500):
        j=rng.randrange(N);r=P.R[j]
        if r.prepare_to is not None:
            # Fenced mutation may remain in progress but cannot publish.
            row=P.support(j,t,rng.randrange(5)!=0)
        elif r.tail and rng.randrange(2):
            row=P.retire(j,min(r.tail),t,rng.randrange(4)!=0)
        else:
            h=rng.randrange(12)
            if h!=r.current:P.prepare(j,h)
            row=None
        if row:pending.append(row)
        # Delivery may be delayed and reordered across helpers. Supplying
        # a later row on the same helper before the gap is rejected.
        if pending and rng.randrange(5):
            m=pending[rng.randrange(len(pending))]
            before=V.nwrite
            if V.deliver(m):
                assert V.nwrite==before+1
                pending.remove(m);updates+=1
            else:assert V.nwrite==before
        for _ in range(2):
            h=rng.randrange(12);tk=P.close_scope(h,t,t+1)
            answer=V.consume(h,t,t+1,tk)
            if answer is not None:
                assert answer==P.affected(h)
                count+=1
            else:blocked+=1
    print(updates,"delivered physical scoped mutations")
    print(count,"exact accepted scope checks and",blocked,"expected local gap refusals")
if __name__=="__main__":derived_field();tests()
