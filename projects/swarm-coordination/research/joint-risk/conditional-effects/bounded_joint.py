"""An exact paired calibration box, not an independently sampled prior."""
from fractions import Fraction as F
from itertools import product
from random import Random
from coupled import cut,exact

def dominant(boxes):
    # Every label's feasible ranges are paired by incidence 0<=C<=L<=1.
    # The kind of source mixing considered here admits all these label corners
    # jointly; this does not assume risk-law selection is split across cuts.
    pairs=[]
    for lo,hi,c,d in boxes:
        assert 0<=lo<=hi<=1 and 0<=c<=d<=1 and c<=hi
        C=min(hi,d);L=max(lo,C)
        pairs.append((L,C))
    return tuple(zip(*pairs))

def enumerate_threshold(boxes,w,cutoff):
    # Rational cell enumerate at every feasible corner of rectangle
    # intersected with the event-subset incidence half-space.
    tables=[]
    for lo,hi,c,d in boxes:
        V={(x,y) for x,y in product((lo,hi),(c,d)) if y<=x}
        for t in {lo,hi,c,d}:
            if lo<=t<=hi and c<=t<=d:V.add((t,t))
        tables.append(sorted(V))
    return all(cut(L,C,w,cutoff) for L,C in map(lambda items:tuple(zip(*items)),product(*tables))
               if sum(L)>0)

def ratio_guard(boxes,w):
    L,C=dominant(boxes)
    if sum(L)==0:return F(0)
    return exact(L,C,w)

def main():
    rng=Random(37284)
    for h in range(340):
        raw=[]
        for _ in range(rng.randrange(2,5)):
            l,h=sorted(F(rng.randrange(11),10) for i in range(2))
            c=F(rng.randrange(int(10*h)+1),10)
            d=F(rng.randrange(int(10*c),11),10)
            raw.append((l,h,c,d))
        w=F(rng.randrange(10),10)
        q=F(rng.randrange(21),20)
        r=ratio_guard(raw,w)
        assert (r<=q)==enumerate_threshold(raw,w,q)
    # Missing support on one reported phase and partial calibration of
    # contact on another. Raw C upper endpoint may not be realizable with L.
    state=((F(1,4),F(1,3),F(0),F(1,2)),
           (F(0),F(1,5),F(0),F(1,10)),
           (F(3,5),F(4,5),F(1,5),F(2,5)))
    L,C=dominant(state)
    assert C[0]==L[0]==F(1,3)
    p=ratio_guard(state,F(1,4))
    print('340 exact paired support cases; realized witness worst cap',p,'at',L,C)

if __name__=='__main__':main()
