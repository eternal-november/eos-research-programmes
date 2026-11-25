"""Standalone rational checker: no optimization backend or source replay needed."""
import json,sys
from fractions import Fraction
from pathlib import Path

def dot(a,b):return sum(x*y for x,y in zip(a,b))
def validate(row):
    f=lambda k:[Fraction(v) for v in row[k]]
    H=row["H"];z=f("z");l=f("lower");u=f("upper");p=f("weights")
    w=f("witness");a=f("policy");s=f("slack");e=f("eta");q=f("dual")
    beta=Fraction(row["beta"]);cap=Fraction(row["cap"])
    m=len(p);r=len(H)
    assert all(len(v)==m for v in (l,u,w,a,s,q,*H)) and len(z)==len(e)==r
    assert len(z)==r and [dot(row,w) for row in H]==z
    assert all(0<=lo<=y<=hi for lo,y,hi in zip(l,w,u))
    assert all(x>=0 for x in p) and sum(p)==1 and cap>=0
    assert all(0<=v<=1 for v in a) and all(t>=0 for t in s)
    assert all(a[i]<=s[i]+sum(H[j][i]*e[j] for j in range(r)) for i in range(m))
    d=[y-dot(k,l) for k,y in zip(H,z)]
    c=[j-i for i,j in zip(l,u)]
    assert dot(l,a)+dot(d,e)+dot(c,s)<=cap
    assert beta>=0 and all(0<=v<=beta*c_i for v,c_i in zip(q,c))
    assert [dot(row,q) for row in H]==[beta*u for u in d]
    assert dot(p,a)==beta*cap+sum(max(0,p_i-q_i-beta*l_i) for p_i,q_i,l_i in zip(p,q,l))
    assert dot(p,a)==Fraction(row["utility"])
    return m
if __name__=='__main__':
    sizes=[validate(row) for row in json.loads(Path(sys.argv[1]).read_text())]
    print('Certified optimum for context counts:',sizes)
