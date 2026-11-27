"""Exact fixed-width export for a future named equal-length audit window."""
from functools import lru_cache
from itertools import product
import json

def moving_or(word,r):
    return tuple(int(any(word[j:j+r])) for j in range(len(word)-r+1))

def model(m,r):
    # State -1 is start, 0 is zero, 1..r is capped trailing run.
    # Initial one skips to r: the first run touches the left boundary.
    def nxt(state,b):
        if b:
            return r if state==-1 else min(r,state+1)
        return 0 if state in (-1,0,r) else None
    @lru_cache(None)
    def count(left,state):
        if left==0:return 1
        return sum(count(left-1,s) for s in (nxt(state,0),nxt(state,1)) if s is not None)
    def rank(word):
        assert len(word)==m
        z=0;s=-1
        for i,b in enumerate(word):
            zero=nxt(s,0)
            if b and zero is not None:z+=count(m-i-1,zero)
            s=nxt(s,b)
            if s is None:return None
        return z
    def unrank(a):
        assert 0<=a<count(m,-1)
        s=-1;o=[]
        for i in range(m):
            zero=nxt(s,0);v=0 if zero is None else count(m-i-1,zero)
            b=int(a>=v)
            if b:a-=v
            o.append(b);s=nxt(s,b)
        assert a==0
        return tuple(o)
    return count(m,-1),rank,unrank

def from_runs(v,r):
    m=len(v)
    return tuple(int(all(v[i] for i in range(max(0,j-r+1),min(j,m-1)+1)))
                 for j in range(m+r-1))

def main():
    checked=0;sections=[]
    for n in range(1,13):
        for r in range(1,n+1):
            m=n-r+1
            reachable={moving_or(x,r) for x in product((0,1),repeat=n)}
            total,rank,unrank=model(m,r)
            assert total==len(reachable)
            for v in product((0,1),repeat=m):
                a=rank(v)
                assert (a is not None)==(v in reachable)
                assert (moving_or(from_runs(v,r),r)==v)==(v in reachable)
                if a is not None:assert unrank(a)==v
                checked+=1
            assert [unrank(i) for i in range(total)]==sorted(reachable)
    for n in (6,12,24,48,100):
        for r in (1,2,3,5,n):
            if r>n:continue
            total,rank,unrank=model(n-r+1,r)
            sections.append([n,r,total,(total-1).bit_length()])
    # A longer-window query covers the union of its contained minimum windows:
    # knowing the shortest authorized width suffices for any named longer width.
    longer=0
    for n in range(1,10):
        for x in product((0,1),repeat=n):
            for s in range(1,n+1):
                y=moving_or(x,s)
                for r in range(s,n+1):
                    assert moving_or(y,r-s+1)==moving_or(x,r)
                    longer+=1
    print(json.dumps({'verified_output_words':checked,'longer_queries':longer,'counts':sections,
                       'scope':'exact answers after the recurrent history'},sort_keys=True,separators=(',',':')))
if __name__=='__main__':main()
