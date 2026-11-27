"""Exact authored laws over native controlled tape results."""
from collections import Counter
from functools import cache
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json
import sys

def laws(law):
    # W=early executable task class. H=0 TX failure (no draw), H=1
    # RX failure (one draw). A and B are physical visit marks.
    for W,H,B,X in product((0,1), repeat=4):
        A=(W^law) if H else X
        yield W,H,A,B

def dot(log, keys):
    return Counter(tuple(x[i] for i in keys) for x in log)

def project(L,mode,table):
    return [(W,H,A,B,*table[H,A,B,mode]) for W,H,A,B in laws(L)]

def errors(n):
    # Direct total variation / Bayes discrimination with equal priors.
    # Align each diagnostic report to the early class W.
    noisy=F(0)
    for bits in product((0,1),repeat=n):
        k=sum(bits)
        noisy+=min(F(1,4)**k*F(3,4)**(n-k),F(3,4)**k*F(1,4)**(n-k))/2
    # Direct transcript probabilities for eligible, ineligible-independent.
    marked=F(0)
    for symbols in product((-1,0,1),repeat=n):
        likelihood=[F(1),F(1)]
        for sym in symbols:
            for h in (0,1):
                likelihood[h]*=F(1,2) if sym in (-1,h) else 0
        marked+=min(likelihood)/2
    assert marked==F(1,2)**(n+1)
    return str(noisy),str(marked)

@cache
def opt(n,p,c,phase):
    stop=min(p,1-p)/4
    if not n or not stop:
        return stop
    if phase:
        test=c+opt(n-1,p,c,phase)/2  # informative half the time
    else:
        z=F(1,4)*p+F(3,4)*(1-p)
        test=c+z*opt(n-1,F(1,4)*p/z,c,phase)+(1-z)*opt(
             n-1,F(3,4)*p/(1-z),c,phase)
    return min(stop,test)

def costs():
    for n,c in product(range(9),(F(0),F(1,64),F(1,32),F(1,16),F(1,8))):
        # Independently enumerate maximum pre-purchased number of trials,
        # conditional on immediate termination after a conclusive phase.
        expectation=min(sum((c/F(2)**k for k in range(i)),F(0))+F(1,8)/2**i
                        for i in range(n+1))
        assert expectation==opt(n,F(1,2),c,True)
        assert expectation<=opt(n,F(1,2),c,False)
    # Analytical all-horizon induction for this fixed cost:
    # |log_3 posterior odds|>=2 has loss below the price of one test.
    # At |log odds|=1 a trial can move to 0 or 2.
    c=F(1,32)
    assert F(1,40)<c and c+F(5,8)*F(1,40)+F(3,8)*F(3,32)>F(1,16)
    assert c+F(1,16)==F(3,32)
    assert all(opt(n,F(1,2),c,False)==F(3,32) for n in range(1,9))
    return [[str(opt(n,F(1,2),F(1,32),b)) for b in (False,True)]
            for n in range(9)]

def main():
    records=[tuple(map(int,s.split())) for s in Path(sys.argv[1]).read_text().splitlines()]
    table={r[:4]:r[4:] for r in records}
    assert len(table)==16
    x0,x1=[project(L,0,table) for L in (0,1)]
    y0,y1=[project(L,1,table) for L in (0,1)]
    # Z includes exact phase and number of draws, but not the censored
    # mark's value. Side report always remains failed in the two laws.
    assert dot(x0,(0,1,4,5,6))==dot(x1,(0,1,4,5,6))
    assert dot(x0,(2,3))==dot(x1,(2,3)) # both full unconditional tape laws match
    p=[[F(sum(r[4] for r in y if r[0]==W),8) for W in (0,1)] for y in (y0,y1)]
    assert p==[[F(1,4),F(3,4)],[F(3,4),F(1,4)]]
    # Law knows whether to reserve per early class; the camera/charge
    # diagnosis comes after that decision and is not available for it.
    surveys=[(a,b) for a,b in product((0,1),repeat=2)]
    def surplus(prep, rates):
        return sum((F(1,2)*s*(F(1,2)-t) for s,t in zip(prep,rates)),F(0))
    pol=[[surplus(a,rate) for a in surveys] for rate in p]
    assert all(max(xs)==F(1,8) for xs in pol)
    assert max(map(min,zip(*pol)))==0  # mixture cannot help by mirrored laws
    out=dict(native_rows=len(records),old_first_by_class=[[str(x) for x in row] for row in p],
             law_known_gain="1/8",unidentified_robust_gain="0",
             receipt_only_vs_qualified=[errors(i) for i in range(9)],
             one_test_margin="1/32", adaptive_losses=costs())
    print(json.dumps(out,sort_keys=True,indent=2))
if __name__=="__main__":main()
