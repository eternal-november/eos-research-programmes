#!/usr/bin/env python3
from itertools import product
from pathlib import Path
import json

def fields(v,f,r,phase):
    return {t:(t>=v,not(r and t==2 and phase==0),not(r and t==2),t>=f)
            for t in range(1,5)}

def main():
    m={}
    starts=[0]*5
    valid=[0]*5
    false=[0]*5
    for line in Path(__file__).with_name("NATIVE.txt").read_text().splitlines():
        v,f,r,h,j,k,a,lawful,encoded=map(int,line.split())
        moves=fields(v,f,r,j)
        ref=0
        for c,p,e,q in moves.values():
            ref=16*ref+8*c+4*p+2*e+q
        assert ref==encoded
        tests=[
            lambda c,p,e,q:True,
            lambda c,p,e,q:c,
            lambda c,p,e,q:c and q,
            lambda c,p,e,q:c and p and q,
            lambda c,p,e,q:c and e and q
        ]
        want=next((t for t,x in moves.items() if t<=h and tests[k](*x)),0)
        assert a==want and bool(lawful)==(not a or (moves[a][0] and moves[a][2] and moves[a][3]))
        starts[k]+=bool(a)
        valid[k]+=bool(a and lawful)
        false[k]+=bool(a and not lawful)
        m[v,f,r,h,j,k]=a,lawful
    assert len(m)==720 and not false[4]
    a,b=fields(1,2,0,0)[1],fields(2,1,0,0)[1]
    assert a==(True,True,True,False) and b==(False,True,True,True)
    assert all({a[i],b[i]}.issuperset({True}) for i in range(4))
    assert not any(map(all,(a,b)))
    # Both further cuts preserve the old C callback and actual clearance.
    assert m[2,2,1,2,0,2]==(2,0)
    assert m[2,2,1,2,0,4]==(0,1)
    assert m[2,2,1,2,1,3]==(2,0)
    assert m[2,2,1,2,1,4]==(0,1)
    assert m[2,2,1,3,1,4]==(3,1)
    # Masking: the report loss/absence can already prevent service,
    # but discovering both C and clearance only removes that mask.
    visible=[]
    for v,f in product((1,2,3),repeat=2):
        x=fields(v,f,0,1)[2]
        if x[0] and x[3]:
            visible.append((v,f))
            assert all(x) and not fields(v,f,1,1)[2][2]
    at_two={(c,e,q) for v,f,r in product((1,3),(1,3),(0,1))
            for c,p,e,q in [fields(v,f,r,1)[2]]}
    assert len(at_two)==8
    assert {all(x) for x in at_two}=={False,True}
    for i in range(3):
        bad=tuple(j!=i for j in range(3))
        assert bad in at_two and not all(bad)
        assert bad[:i]+bad[i+1:]==(True, True)
    print(json.dumps(dict(native_rows=len(m),starts=starts,lawful_starts=valid,
                          illegal_starts=false,
                          retirement_matters_at_two=visible,
                          qualified_triplets_at_two=len(at_two)),sort_keys=True))
if __name__=="__main__":
    main()
