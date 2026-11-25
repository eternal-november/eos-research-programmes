"""Exact arithmetic on published initial pose and an authored rest-to-rest model."""
from fractions import Fraction as Q
from pathlib import Path
from hashlib import sha1
from itertools import combinations

def sub(a,b):return tuple(x-y for x,y in zip(a,b))
def add(a,b):return tuple(x+y for x,y in zip(a,b))
def mul(s,a):return tuple(s*x for x in a)
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def sq(a):return dot(a,a)
def qcoord(line):
    return tuple(Q(x.strip()) for x in line.strip().rstrip(",").strip("[]").split(","))
src=Path("scenario.py.upstream").read_bytes()
assert sha1(f"blob {len(src)}\0".encode()+src).hexdigest()=="193319e4aba9814f8d6989409700ab3618d245d9"
raw=src.decode().splitlines()
P=[qcoord(l) for l in raw[292:297]]
R=Q("1.65"); C=Q("0.45")
def comps(d):
    active=set(range(5))-{d}
    graph={i:{j for j in active if i!=j and sq(sub(P[i],P[j]))<R*R} for i in active}
    group=[]
    while active:
        v={min(active)}
        while True:
            u=v|set().union(*(graph[i] for i in v))
            if u==v:break
            v=u
        group.append(v);active-=v
    return group
assert comps(1)==[{0},{2,3,4}]
assert comps(3)==[{0,1,2},{4}]
delta=sub(P[4],P[0]); s2=sq(delta)
middle=mul(Q(1,2),add(P[0],P[4]))
# Relay uses closed balls in the exact model. Rational witnesses just
# inside them certify the displayed upper time even for strict edges.
lam=Q("0.03960075")
row=[add(middle,mul(sign*lam,delta)) for sign in (-1,1)]
for i,x in zip((0,4),row):
    assert sq(sub(x,P[i]))<R**2
    assert sq(sub(x,P[2]))<R**2
standby_shift_bound=Q("0.142")
assert lam**2*s2<standby_shift_bound**2
assert all(sq(sub(middle,p))>(C+standby_shift_bound)**2 for p in P)
low,high=Q("0.7534532"),Q("0.753454")
# a=1. T*=sqrt(2*(sqrt(s2)-2R)); squared comparisons avoid float.
assert (low**2/2+2*R)**2<s2
assert lam**2*s2<(high**2/4)**2
print("Unit-acceleration motion time after a truthful identity:",
      str(float(low)),str(float(high)))
# Independent dynamic programming in a discrete acceleration lattice.
# Positions doubled; one unit step increments doubled position by 2*v+a.
cases=0
for n in range(1,15):
    for cap in range(1,5):
        for initial_v in range(-cap*n,cap*n+1):
            frontier={initial_v:(0,0)}
            for t in range(n):
                nxt={}
                left=n-t-1
                for v,(lo,hi) in frontier.items():
                    for acc in range(-cap,cap+1):
                        w=v+acc
                        if abs(w)>cap*left:continue
                        p,q=lo+2*v+acc,hi+2*v+acc
                        if w in nxt:p,q=min(p,nxt[w][0]),max(q,nxt[w][1])
                        nxt[w]=p,q
                frontier=nxt
            lo,hi=frontier[0]
            assert hi-lo<=cap*n*n
            if initial_v==0:assert hi-lo==cap*(n*n-(n%2))
            cases+=1
print("Discrete direct spread checks with arbitrary common initial velocity:",cases)
