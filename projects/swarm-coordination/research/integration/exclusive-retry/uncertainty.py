"""Exact finite compilation of continuously uncertain release observations."""
from fractions import Fraction as F
from functools import lru_cache
from math import inf
from random import Random
from timed_evidence import opt

def representatives(failures,error):
    ends=sorted({F(t)+sgn*error for _,_,t in failures for sgn in (-1,1)})
    return sorted(set(ends+[(a+b)/2 for a,b in zip(ends,ends[1:])]))

def cells(failures,error):
    # For each true release interval, include every equality-boundary and
    # every open region between endpoints. Hits may include several worlds.
    reps=representatives(failures,error)
    return {tuple((w,end) for w,end,d in failures if abs(y-d)<=error)
            for y in reps}-{()}

def exact(worlds,error):
    n=len(worlds[0])
    @lru_cache(None)
    def game(rows,left):
        vals=[]
        for k in left:
            finished=[];failed=[]
            for w,t in rows:
                passed,d=worlds[w][k]
                if passed:finished.append(t+d)
                else:failed.append((w,t+d,d))
            successor=tuple(j for j in left if j!=k)
            vals.append(max(finished+[game(b,successor) for b in cells(failed,error)],default=0))
        return min(vals,default=inf)
    return game(tuple((i,0) for i in range(len(worlds))),tuple(range(n)))

def raw_grid(worlds,error):
    # For integer durations and a rational radius on a regular lattice,
    # oversample twice the denominator so both endpoints and open cells
    # are captured. Each world may yield any of those actual readings.
    grid=F(1,2*error.denominator)
    reading=lambda d:tuple(F(d)-error+j*grid for j in range(4*error.numerator+1))
    from itertools import product
    expanded=[]
    for w in worlds:
        opts=[(None,) if ok else reading(d) for ok,d in w]
        expanded.extend((w,y) for y in product(*opts))
    @lru_cache(None)
    def game(variants,left):
        best=inf
        for k in left:
            successes=[];facts={}
            for ix,prior in variants:
                w,y=expanded[ix];ok,d=w[k]
                if ok:successes.append(prior+d)
                else:facts.setdefault(y[k],[]).append((ix,prior+d))
            next=tuple(i for i in left if i!=k)
            best=min(best,max(successes+[game(tuple(row),next) for row in facts.values()],default=0))
        return best
    return game(tuple((i,0) for i in range(len(expanded))),tuple(range(len(worlds[0]))))

def main():
    worlds=(
        ((False,1),(True,1),(False,5)),
        ((False,2),(False,5),(True,1)),
        ((True,1),(False,5),(False,5)))
    for k in (F(0),F(1,4),F(49,100),F(1,2),F(3,4),F(2)):
        a=exact(worlds,k)
        assert a==(3 if k<F(1,2) else 7)
        print('clock radius',k,'worst verified completion',a)
    rng=Random(963251);n=0
    for _ in range(170):
        ws=tuple(tuple((bool(rng.randrange(2)),rng.randrange(1,5))
                       for k in range(3)) for w in range(rng.randrange(2,5)))
        for e in (F(0),F(1,4),F(1,2),F(1)):
            assert exact(ws,e)==raw_grid(ws,e)
            if e==0:assert exact(ws,e)==opt(ws,True)[0]
            n+=1
    print(n,'exact comparisons against expanded immutable time-reading histories')
if __name__=='__main__':main()
