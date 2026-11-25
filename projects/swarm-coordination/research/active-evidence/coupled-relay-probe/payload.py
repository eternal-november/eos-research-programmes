"""Test the semantic fields needed after a probe, with identical delay/actuation."""
from factored import *
from itertools import product

def colorable(W,k,station=Q):
    slots=[]
    for w in W:
        s,stock=phase0(w)
        s=effect(w,State(pos=station),PROBE,0,stock)
        slots.append((w,stock,s))
    for label in product(range(k),repeat=len(W)):
        ok=True
        for l in set(label):
            cohort=[item for item,t in zip(slots,label) if l==t]
            ok &= bool(assignment(cohort) and any(covers(cohort,r) for r in (L,R)))
        if ok:return label

def run():
    paired=(World(L,0),World(R,2))
    independent=tuple(World(exit,f) for exit,f in product((L,R),(0,2)))
    assert not colorable(paired,1) and colorable(paired,2)
    assert not colorable(independent,3) and colorable(independent,4)
    assert not colorable(paired,2,P)
    assert not colorable(independent,4,P)
    print("correlated source: 2 output classes; factorized source: 4")
    print("shared-feed probe: more labels cannot restore a physically missing slot")
if __name__=="__main__":run()
