"""Exact full-state law checks for pre-query one-way risk messages."""
from fractions import Fraction as F
from itertools import product
from math import comb
import json

def character(t,x):
    return -1 if (t&x).bit_count()%2 else 1

def basis(n,k,menu):
    states=tuple(range(1<<n))
    chi=[[character(t,x) for x in states] for t in menu]
    # Named assignments are determined by these all-ones constraints.
    small=[tuple(x for x in states if x&s==s)
           for s in states if s.bit_count()<=k]
    assert all(sum(a[x] for x in z)==0 for z in small for a in chi)
    avoid=[tuple(x for x in states if not x&s) for s in menu]
    for i,s in enumerate(menu):
        for j,t in enumerate(menu):
            assert sum(chi[j][x] for x in avoid[i])==(len(avoid[i]) if t&s==t else 0)
    return states,chi,small,avoid

def fixed():
    n,k,m,h=6,2,3,1
    menu=tuple(s for s in range(1<<n) if s&h==h and s.bit_count()==m)
    states,chi,small,avoid=basis(n,k,menu)
    d=len(menu); assert d==comb(n-1,m-1)==10
    start=2*d; den=start*len(states)
    cap=F((1<<m)-1,10*(1<<m))
    gap=F(1,10*(1<<m)*start)
    words=set()
    for s in product((-1,1),repeat=d):
        w=[start+sum(v*a[x] for v,a in zip(s,chi)) for x in states]
        assert min(w)>=d and sum(w)==den
        assert all(sum(w[x] for x in z)==start*len(z) for z in small)
        risk=tuple(F(den-sum(w[x] for x in z),den*10) for z in avoid)
        assert risk==tuple(cap-v*gap for v in s)
        answer=tuple(r<=cap for r in risk)
        assert answer==tuple(v==1 for v in s)
        words.add(answer)
    assert len(words)==(1<<d)
    return dict(sites=n,diagnostic_order=k,bundle_sites=m,earlier_sites=h.bit_count(),
                cap=str(cap),distance_to_cap=str(gap),menus=len(words),bits=d)

def nested():
    n,k,M=5,1,3
    menu=tuple([3,7,11,15,31])
    states,chi,small,avoid=basis(n,k,menu)
    d=len(menu)
    start=2*d*(M-1);den=start*len(states)
    seen=set()
    out=[]
    for coeff in product(range(M),repeat=d):
        w=[start+sum(v*a[x] for v,a in zip(coeff,chi)) for x in states]
        assert min(w)*2>=start and sum(w)==den
        assert all(sum(w[x] for x in z)==start*len(z) for z in small)
        values=tuple(den-sum(w[x] for x in z) for z in avoid)
        # Recover coefficient indices by triangular subtraction without using the original signs.
        got={}
        for s,fail,z in zip(menu,values,avoid):
            delta=den-fail-start*len(z)
            assert delta%len(z)==0
            got[s]=delta//len(z)-sum(v for t,v in got.items() if t&s==t)
        assert tuple(got[s] for s in menu)==coeff
        seen.add(values);out.append(values)
    assert len(seen)==M**d
    # Between any two different union-risk vectors a rational midpoint
    # cap at a distinguishing query has different admission answers.
    pairs=0
    for i,v in enumerate(out):
        for w in out[:i]:
            x,y=next((x,y) for x,y in zip(v,w) if x!=y)
            # Compare the two rational risks with midpoint without rounding.
            assert (2*x<=x+y)!=(2*y<=x+y)
            pairs+=1
    return dict(sites=n,diagnostic_order=k,queries=d,levels=M,law_count=len(seen),
                distinct_pair_checks=pairs,fixed_length_bits=(len(seen)-1).bit_length())

if __name__=="__main__":
    print(json.dumps({"fixed_cap":fixed(),"queried_cap":nested()},indent=2,sort_keys=True))
