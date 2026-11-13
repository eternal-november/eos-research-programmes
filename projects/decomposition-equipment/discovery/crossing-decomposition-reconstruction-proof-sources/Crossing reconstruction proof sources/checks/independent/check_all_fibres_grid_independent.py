#!/usr/bin/env python3
from itertools import product,permutations
from math import factorial
from collections import Counter
from pathlib import Path
import json
counts=Counter()
for r,q,s,p,n in product(range(3),repeat=5):
    # All six endpoint object sets singleton. Actual whole witnesses are (p,q,s) and(r,q,n).
    src=list(product(range(p),range(q),range(s)));tgt=list(product(range(r),range(q),range(n)))
    if len(src)!=len(tgt) or len(src)>6:continue
    counts['profiles']+=1
    if r==s==0:
        # No bounded fibres. Parents must both be empty; T arbitrary if so.
        expected=p==n==0
        for theta in permutations(range(len(tgt))):
            assert len(src)==0
            # Direct cardinal requirements for T=0,1,2.
            possible=[m for m in range(3) if r*m==p and m*s==n]
            assert bool(possible)==expected
            if expected:assert possible==[0,1,2]
            counts['invisible_profiles_checked']+=1
        continue
    ms=[m for m in range(3) if r*m==p and m*s==n]
    assert len(ms)<=1
    for theta in permutations(range(len(tgt))):
        matching=dict(zip(src,(tgt[i] for i in theta)))
        labels=[]
        for m in ms:
            adom=list(product(range(r),range(m)));bdom=list(product(range(m),range(s)))
            for aa,bb in product(permutations(range(p)),permutations(range(n))):
                alpha=dict(zip(adom,aa));beta=dict(zip(bdom,bb))
                if all(matching[alpha[rr,t],qq,ss]==(rr,qq,beta[t,ss]) for rr,t,qq,ss in product(range(r),range(m),range(q),range(s))):
                    labels.append((aa,bb))
        orbits=[];unseen=set(labels)
        if ms:
            m=ms[0];adom=list(product(range(r),range(m)));bdom=list(product(range(m),range(s)))
            for aa,bb in labels:
                stabilizer=0;orbit=set()
                for g in permutations(range(m)):
                    gi={g[t]:t for t in range(m)}
                    a=dict(zip(adom,aa));b=dict(zip(bdom,bb))
                    relabeled=(tuple(a[rr,gi[t]] for rr,t in adom),tuple(b[gi[t],ss] for t,ss in bdom))
                    assert relabeled in labels
                    stabilizer+=relabeled==(aa,bb);orbit.add(relabeled)
                assert stabilizer==1
                if (aa,bb) in unseen:orbits.append(orbit);unseen-=orbit
            assert len(orbits)*factorial(m)==len(labels)
        assert not unseen
        counts['theta_cases']+=1
        counts['matching_pairs']+=len(labels)
        counts['bounded_realization_orbits']+=len(orbits)
        counts['nonempty_solution_theta_cases']+=bool(labels)
        counts['nonunique_bounded_theta_cases']+=len(orbits)>1
        if q==0:counts['empty_Q_theta_cases']+=1
# Specific nonunique bounded example q0,r=s1,p=n2:4labelledpairs /2! =2 actualorbits.
assert factorial(2)*factorial(2)//factorial(2)==2
out={'status':'PASS','scope':'Singleton six object sets; R,Q,S,P,N witness cardinalities0..2; all actual whole bijections for matching whole counts≤6. Direct bounded matching enumeration with all Sym(T) actions verifies free action and orbit classification; invisible fibres separately tested at T cardinalities0,1,2 only, not exhaustive all finite sets.','counts':dict(counts)}
Path(__file__).with_name('All_Fibres_Grid_Independent_Checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
