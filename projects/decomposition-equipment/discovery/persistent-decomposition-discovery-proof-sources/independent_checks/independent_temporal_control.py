#!/usr/bin/env python3
"""Independent direct multiset/product and closed-loop trace checks. Standard library only."""
from itertools import product, permutations
from collections import Counter
from pathlib import Path
import json, math

def step(i,b,twists): return ((i+1)%len(twists), b^twists[i])
def whole_edges(twists,k=1,keep=None):
    m=len(twists); out=Counter()
    for i,b in product(range(m),range(2)):
        if keep is not None and i not in keep: continue
        j,c=i,b
        for _ in range(k): j,c=step(j,c,twists)
        out[(i,b,j,c)]+=1
    return out

def exact_count_factors(twists,k=1,keep=None,allow_two=True):
    m=len(twists); whole=whole_edges(twists,k,keep); count=0
    # Enumerate all context-respecting two-state encodings, and all event
    # multiplicities 0..2, including nondeterminism and duplicate records.
    for labels in product(range(2),repeat=m):
        encoded=Counter({(i,b^labels[i],j,c^labels[j]):n for (i,b,j,c),n in whole.items()})
        for mult in product(range(3 if allow_two else 2),repeat=4):
            expected=Counter()
            for i in range(m):
                if keep is not None and i not in keep:continue
                j=(i+k)%m
                for z,zp in product(range(2),repeat=2):
                    if mult[2*z+zp]: expected[(i,z,j,zp)]=mult[2*z+zp]
            if encoded==expected:count+=1
    return count

def identity_possible(twists,keep):
    m=len(twists)
    return any(all((b^p[i])==(c^p[j]) for i,b,j,c in whole_edges(twists,keep=keep))
               for p in product(range(2),repeat=m))

def execute(m,h,policy,memory=False,resample=False):
    # Initial memory independent of h. h visible only while i=0.
    # Wait does not advance time/state; actions at non-final stations do not
    # store a signal or modify b. Goal is completing one lap with b unchanged.
    i=b=q=0;seen=set();ticks=0
    while True:
        state=(i,b,q)
        if state in seen:return False,ticks,'cycle'
        seen.add(state)
        obs=(i,h if i==0 else None)
        act=policy(q,obs) if memory else policy[obs]
        if act=='wait': return False,ticks,'cycle'
        nq=h if memory and i==0 else q
        if i==m-1:
            possible_h=(0,1) if resample else (h,)
            return all((b^hh^act)==0 for hh in possible_h),ticks+1,'terminal'
        i+=1;q=nq;ticks+=1

def main():
    exact_instances=0; exact_patterns=[]
    for m in (2,3,4):
        for twists in product(range(2),repeat=m):
            count=exact_count_factors(twists)
            expected=(m%2==1 or sum(twists)%2==0)
            assert bool(count)==expected
            exact_instances+=1
            exact_patterns.append({'m':m,'twists':list(twists),'factor_count':count})
    proper_checks=0
    for m in range(2,7):
        twists=(0,)*(m-1)+(1,)
        for mask in range((1<<m)-1):
            keep={i for i in range(m) if mask&(1<<i)}
            assert identity_possible(twists,keep);proper_checks+=1
    macro=[]
    for m in (2,3,4):
        twists=(0,)*(m-1)+(1,)
        count=exact_count_factors(twists,k=m)
        assert count>0
        macro.append({'m':m,'sample_length':m,'exact_macro_factors':count})
    controls=[]
    for m in range(2,6):
        obs=[(0,0),(0,1)]+[(i,None) for i in range(1,m)]
        tested=wins=0
        for vals in product((0,1,'wait'),repeat=len(obs)):
            pol=dict(zip(obs,vals));tested+=1
            wins+=all(execute(m,h,pol)[0] for h in (0,1))
        assert wins==0
        policy=lambda q,o: q if o[0]==m-1 else 0
        traces=[execute(m,h,policy,memory=True) for h in (0,1)]
        assert all(ok and ticks==m for ok,ticks,_ in traces)
        assert not all(execute(m,h,policy,memory=True,resample=True)[0] for h in (0,1))
        controls.append({'m':m,'memoryless_tables_including_wait':tested,'winning':wins,'two_memory_success':True,'resampling_control_rejected':True})
    # Independent direct test of anchored-cut coprime reflection. Product maps
    # are explicitly constructed; no conjugacy/root routine is imported.
    def compose(f,g): return tuple(f[g[x]] for x in range(4))
    def power(f,n):
        out=tuple(range(4))
        for _ in range(n):out=compose(f,out)
        return out
    products=set()
    for a,b in product(product(range(2),repeat=2),repeat=2):
        products.add(tuple(2*a[x//2]+b[x%2] for x in range(4)))
    coprime_tests=0
    for f in permutations(range(4)):
        for r,s in product(range(1,7),repeat=2):
            if math.gcd(r,s)!=1:continue
            if power(f,r) in products and power(f,s) in products: assert f in products
            coprime_tests+=1
    transient=(0,0,1,0)
    assert transient not in products
    assert power(transient,2) in products and power(transient,3) in products
    calibrated=0;uncalibrated_defects=0
    for m in range(2,6):
        for i,h,q,b in product(range(m),range(2),range(2),range(2)):
            ip=(i+1)%m; qp=h if i==0 else q
            bp=b^(h^q if i==m-1 else 0)
            if i==0 or q==h:
                assert ip==0 or qp==h
                assert bp==b
                calibrated+=1
            elif i==m-1:
                assert bp!=b;uncalibrated_defects+=1
    out={'calibrated_invariant_states_checked':calibrated,
         'uncalibrated_identity_factor_defects':uncalibrated_defects,
         'coprime_sample_cases':coprime_tests,'noninvertible_negative_control':True,
         'independent_exact_multiset_instances':exact_instances,
         'event_multiplicities_tested':[0,1,2],
         'proper_edge_views':proper_checks,'macro_factor_results':macro,
         'controller_results':controls,'all_checks_passed':True}
    p=Path(__file__).with_suffix('.json');p.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
