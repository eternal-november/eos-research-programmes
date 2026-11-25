"""Find the minimum stationary label alphabet with silence defaults allowed.

Rows: (source state, alarm time, earliest permitted start, latest start).
The label is selected from source state only. No sender knowledge of latency.
"""
from random import Random
from itertools import combinations,product
from collections import defaultdict
from solve import compile_rule

def colors(rows):
    k=max(c for c,*_ in rows)+1
    def default_ok(t):return all(q<=t or lo<=t<=hi for c,q,lo,hi in rows)
    s=next(t for t in range(max(q for c,q,lo,hi in rows)+1) if default_ok(t))
    by_time=defaultdict(list)
    for c,q,lo,hi in rows:
        if q>s:continue
        if q>hi:return s,None
        by_time[q].append((c,lo,hi))
    conflicts=set()
    for q,w in by_time.items():
        for (c,lo,hi),(c1,lo1,hi1) in combinations(w,2):
            if max(q,lo,lo1)>min(hi,hi1):
                if c==c1:return s,None
                conflicts.add((c,c1))
    for m in range(1,k+1):
        for tag in product(range(m),repeat=k):
            if all(tag[i]!=tag[j] for i,j in conflicts):
                return s,tag
    return s,None

def ref(rows):
    k=max(c for c,*_ in rows)+1
    for m in range(1,k+1):
        for label in product(range(m),repeat=k):
            probe=[(lo,hi,q,label[c]) for c,q,lo,hi in rows]
            if compile_rule(probe) is not False:return m
    return None

if __name__=="__main__":
    rng=Random(20261125)
    for _ in range(3000):
        size=rng.randrange(1,6);rows=[]
        for c in range(size):
            anchor=rng.randrange(9)
            for trial in range(rng.randint(1,3)):
                lo=anchor+rng.randrange(3)
                rows.append((c,anchor+rng.randrange(6),lo,lo+rng.randrange(5)))
        cut,tag=colors(rows)
        m=None if tag is None else len(set(tag))
        assert m==ref(rows),(rows,cut,tag,m,ref(rows))
    print("3000 exact comparisons of minimum stationary tag alphabet with silence default")
