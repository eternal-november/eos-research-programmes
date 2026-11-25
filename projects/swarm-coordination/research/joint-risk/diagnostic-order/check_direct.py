"""Independent numerical full-world LP including a labeled-report control."""
from itertools import combinations
from math import comb
import json
import numpy as np
from scipy.optimize import linprog
from replay import law_pair,support_search

def endpoints(A,b,f):
    vals=[]
    for c in (f,-f):
        p=linprog(c,A_eq=A,b_eq=b,bounds=(0,None),method="highs")
        assert p.success
        vals.append(float(f@p.x))
    return tuple(vals)

def state_rows(n,k):
    return np.array([[int(x&s==s) for x in range(2**n)] for s in range(2**n)
                     if s.bit_count()<=k], dtype=float)

def count_rows(n,k):
    return np.array([[comb(x,j) for x in range(n+1)] for j in range(k+1)],dtype=float)

def main():
    comparisons=0
    for n in range(1,8):
        y=np.array([0]+[1]*(2**n-1),dtype=float)
        for k in range(n):
            gap,S=support_search(n,k)
            witness,_=law_pair(S)
            p=np.array([float(witness.get(x.bit_count(),0)/comb(n,x.bit_count()))
                        for x in range(2**n)],dtype=float)
            A=state_rows(n,k);b=A@p
            lo,hi=endpoints(A,b,y)
            assert abs(hi-lo-float(gap))<1e-8
            b=[sum(float(v)*comb(x,j) for x,v in witness.items()) for j in range(k+1)]
            lo2,hi2=endpoints(count_rows(n,k),b,np.array([0]+[1]*n,dtype=float))
            assert abs(lo-lo2)<1e-8 and abs(hi-hi2)<1e-8
            comparisons+=1
    # Two fair independent active coordinates and an identically zero third.
    # The full named two-site reports reveal the third is always zero.
    full=state_rows(3,2);known=np.array([.25,.25,.25,.25,0,0,0,0])
    actual=endpoints(full,full@known,np.array([0,1,1,1,1,1,1,1],dtype=float))
    unlabelled=endpoints(count_rows(3,2),[1,1,.25],np.array([0,1,1,1],dtype=float))
    assert np.allclose(actual,[.75,.75]) and np.allclose(unlabelled,[.75,5/6])
    print(json.dumps({"comparisons":comparisons,"full_named_states":"up to 128",
                      "nonexchangeable_named_report":["3/4","3/4"],
                      "its_aggregated_moments":["3/4","5/6"],
                      "validation":"numerical comparison; sharp results have separate exact certificates"},
                     indent=2,sort_keys=True))
if __name__=="__main__":main()
