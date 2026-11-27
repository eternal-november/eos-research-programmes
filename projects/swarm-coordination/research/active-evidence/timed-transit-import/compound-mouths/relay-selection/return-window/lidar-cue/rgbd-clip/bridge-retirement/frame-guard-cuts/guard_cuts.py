"""Exact frame-cut qualification on a bounded projected Boolean history."""
from itertools import product
from functools import lru_cache
import sys

def residue(first, last, q0, q1, states):
    return (2*(q1-q0)+last-first)%(2*states)

def contains(lo,hi,r,period):
    """Some number in closed [lo,hi] congruent to r."""
    return lo+(r-lo)%period <= hi

def possible(start, end, left, right, H, d, period):
    """Exact possible Boolean values at the frame cut, assuming every <=H flip path fits the source law."""
    assert left>=0 and right>=0 and period>0 and period%2==0
    if d%2!=start^end:
        return frozenset()
    result=set()
    for at_frame in (0,1):
        a=start^at_frame
        b=at_frame^end
        left_max=left-(left-a)%2
        right_max=right-(right-b)%2
        # Feasible segment flip counts form two step-2 integer intervals.
        # Their sum contains every point of the single combined progression.
        if left_max>=a and right_max>=b and contains(a+b,min(H,left_max+right_max),d,period):
            result.add(at_frame)
    return frozenset(result)

@lru_cache(None)
def words(start,n):
    return tuple(tuple([start, *tail]) for tail in product((0,1),repeat=n))

def changes(word):
    return sum(a!=b for a,b in zip(word,word[1:]))

def sample(source):
    patterns=set(); rows=0
    for line in source:
        ops,bits=line.split()
        x=0; ref=[x]
        for c in ops:
            if c in '12':x=int(c=='1')
            ref.append(x)
        w=tuple(map(int,bits))
        assert w==tuple(ref)
        patterns.add(w);rows+=1
    assert rows==4096 and len(patterns)==64
    assert patterns==set(words(0,6))
    return rows

def main():
    rows=sample(sys.stdin)
    queries=0
    for n in range(9):
      for cut in range(n+1):
        for start,end,H,states in product((0,1),(0,1),range(n+1),range(1,7)):
          valid=[(changes(w),w[cut]) for w in words(start,n) if w[-1]==end and changes(w)<=H]
          for d in range(2*states):
            assert possible(start,end,cut,n-cut,H,d,2*states)==frozenset(
                   mid for k,mid in valid if k%(2*states)==d)
            queries+=1
    for H in range(1,513):
        m=H//2+1
        assert residue(0,H%2,0,(H//2)%m,m)==H
        sm=m-1
        if sm:
            assert residue(0,0,0,0,sm)==0
            assert possible(0,0,1,2*sm-1,H,0,2*sm)==frozenset((0,1))
    assert possible(0,0,1,1,2,0,2)==frozenset((0,1))
    assert possible(0,0,1,1,2,0,4)==frozenset((0,))
    assert possible(0,0,1,1,2,2,4)==frozenset((1,))
    # Same bit at both polls, but the new birth before the frame makes the old interpretation wrong.
    print(f'{rows} native callback schedules; 64 guard histories; {queries} exact decoder comparisons')
    print('H=2: same endpoint bits permit two modes; 1 extra token bit distinguishes zero vs two flips')
if __name__=='__main__':
    main()
