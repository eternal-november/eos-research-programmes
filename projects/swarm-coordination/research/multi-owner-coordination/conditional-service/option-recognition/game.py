"""Scope-limited sale of optional civil inspection service under changing authority."""
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product

@dataclass(frozen=True)
class Option:
    issued: bool
    signer_recognized: bool
    actual_old_drains: int
    receipt_at: int
    gate_clear: bool
    grant_expiry: int

def realized(o,decision=4,dwell=2,deadline=6):
    # Start operations only at or after finish of the live old load. Grant
    # expiry applies to the operation; a remote grant on paper is not usable.
    if not (o.issued and o.signer_recognized and o.gate_clear and o.receipt_at<=decision):
        return False
    return max(decision,o.actual_old_drains)+dwell<=min(o.grant_expiry,deadline)

def plant(o,decision=4,dwell=2,deadline=6):
    stores=[{t for t in range(0,o.actual_old_drains)}]
    for t in range(decision,deadline+1):
        if not (o.issued and o.signer_recognized and o.gate_clear and o.receipt_at<=decision):
            return False
        if t+dwell>min(o.grant_expiry,deadline): continue
        if any(t+step in stores[0] for step in range(dwell)): continue
        return True
    return False

def settle(a,v,k,p,safety=True):
    # No enforceable transfer by price alone; both may afford to decline.
    if safety and p is not None and v-p>=a and p>=k:
        return ('joint',v-p,p-k)
    return ('option' if a else 'idle',a,0)

def analyze(v,k,a,q,expose):
    delta=(v-k)*q-a
    if expose:
        # Every lawful purchase earns exactly its outside value; participation
        # occurs because v-a>k, not because of a binding commitment ex ante.
        return ('discriminate',q*a,v-k-q*a)
    if delta>=0: # at exact fee-profit tie select maximal voluntary service
        return ('pool',a,v-a-k)
    return ('screen',q*a,(1-q)*(v-k))

def brute(v,k,a,q,expose):
    # Actual best response, not an invocation of the threshold.
    states=((0,1-q),(a,q))
    groups=tuple((x,) for x in states) if expose else (states,)
    buyer=seller=0
    labels=[]
    for group in groups:
        options=[]
        for p in (None,*range(v+1)):
            live=[(settle(x,v,k,p),mass) for x,mass in group]
            s=sum(x[2]*m for x,m in live)
            b=sum(x[1]*m for x,m in live)
            serv=sum(m for x,m in live if x[0]=='joint')
            options.append((s,serv,b))
        s,srv,b=max(options)
        buyer+=b;seller+=s
        labels.append(srv)
    assert expose or len(labels)==1
    return buyer,seller

def contingent_fallback_certificate(o,active_grant):
    # Grants are represented by a local permission and its executed physical
    # effect, not a branch from the remote price-setter's observation.
    return Option(active_grant,o.signer_recognized,o.actual_old_drains,
                  o.receipt_at,o.gate_clear,o.grant_expiry)

def main():
    c=0
    for signed,recognized,clear,drains,receipt,expiry,dwell in product(
        (False,True),(False,True),(False,True),range(8),range(8),range(3,9),(1,2,3)):
        o=Option(signed,recognized,drains,receipt,clear,expiry)
        assert realized(o,dwell=dwell)==plant(o,dwell=dwell)
        c+=1
    print(c,'actual occupancy/authority/evidence checks')
    c=0
    for v,k,q,expose in product(range(3,15),range(4),[F(i,9) for i in range(1,9)],(False,True)):
        for a in range(1,v-k):
            assert analyze(v,k,a,q,expose)[1:]==brute(v,k,a,q,expose)
            c+=1
    print(c,'posted-price exact response-tree comparisons')
    early=Option(True,True,4,4,True,6)
    late=Option(True,True,4,5,True,6)
    sticky=Option(True,True,5,4,True,6)
    other=Option(True,True,4,4,False,6)
    src=(early,early,sticky,other)
    q=F(sum(realized(t) for t in src),4)
    qlate=F(sum(realized(t) for t in (early,late,sticky,other)),4)
    assert q==F(1,2) and qlate==F(1,4)
    v,k,a,cost,overhead=18,4,6,4,2
    for label,prob,public in (
       ('limited recognition',q,False),('early disclosure to fee setter',q,True),
       ('late local recognition',qlate,False),('no locally usable option',0,False)):
        pricing,revenue,earn=analyze(v,k,a,prob,public)
        prep=revenue>cost and earn>overhead
        print(label, pricing, 'A before setup cost',revenue,'B before admin cost',earn,'mutual prep',prep)
    assert settle(a,v,k,v-a,False)==('option',a,0)
    assert settle(0,v,k,v-a,False)==('idle',0,0)
    # A binding setup-stage fee supplies the same investment incentive even
    # without the option in this fixture, when constitution permits it.
    assert all(settle(a0,v,k,v-a)[0]=='joint' for a0 in (0,a))
    print('non-waivable safety cases refuse shared use; fixed binding tariff ties under wider powers')

if __name__=='__main__':main()
