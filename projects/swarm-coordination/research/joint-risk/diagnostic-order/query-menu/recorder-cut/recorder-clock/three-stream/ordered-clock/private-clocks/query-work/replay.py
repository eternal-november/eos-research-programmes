#!/usr/bin/env python3
"""Independent finite checks of the clock-query model and exact query costs."""
from fractions import Fraction as Q
from functools import lru_cache
from itertools import product, permutations
import json


@lru_cache(None)
def depth(blocks):
    if not blocks or 0 in blocks:
        return 0
    ans=[]
    for i,x in enumerate(blocks):
        if i>0 and x==blocks[i-1]:
            continue
        others=blocks[:i]+blocks[i+1:]
        yes=depth(others)
        no=depth(tuple(sorted(others+(x-1,))))
        ans.append(1+max(yes,no))
    return min(ans)


def group_clock_flags(m, target, d):
    """Check each local pair from its induced stamps, not from the OR formula."""
    allowed=[]
    p2=tuple(permutations(range(2)))
    for j in range(m):
        a=[10*j,10*j+2]
        c=[(10*j+int(j==target),0),(10*j+int(j==target)+2,int(j==target))]
        # Cases use precisely the no-cross-block law from the parent reduction.
        flag={c[p[0]][1] for p in p2
              if all(abs(c[p[k]][0]-a[k]-d)<=Q(9,4) for k in (0,1))}
        assert flag
        if 1 in flag:
            allowed.append(j)
    return set(allowed)


def copy_q(m,d):
    subsets=[group_clock_flags(m,j,d) for j in range(m)]
    return [j in subsets[j] for j in range(m)]


def oracle_truth(m,bits):
    cover=set()
    for i,b in enumerate(bits):
        d=Q(1) if b else Q(1,2)
        cover |= group_clock_flags(m,i//m,d)
    return m+len(cover)


def certificate(m,bits):
    rows=[bits[i:i+m] for i in range(0,m*m,m)]
    if not all(any(r) for r in rows):
        k=next(i for i,r in enumerate(rows) if not any(r))
        return tuple(range(k*m,(k+1)*m))
    return tuple(m*i+r.index(1) for i,r in enumerate(rows))


def eval_cert(m,bits,Qids):
    # A transcript is certifying iff all completions have one verdict.
    yes=[False]*m
    unassigned=[m]*m
    for q in Qids:
        yes[q//m]|=bits[q]==1
        unassigned[q//m]-=1
    unsafe=all(yes)
    safe=any(not y and u==0 for y,u in zip(yes,unassigned,strict=True))
    return unsafe,safe


def expected_cost(m,counts):
    # Run uniform block order; expected within positive row is rank of the first success.
    def within(ones):return Q(m+1,ones+1) if ones else Q(m)
    def decision(order):
        ret=Q(0)
        for ix in order:
            ret+=within(counts[ix])
            if counts[ix]==0:
                break
        return ret
    ways=list(permutations(range(m)))
    return sum(map(decision,ways))/len(ways)


def main():
    arithmetic=0
    for m in range(1,4):
        for d in (Q(0),Q(1,2),Q(3,4),Q(1)):
            assert copy_q(m,d)==[d>=Q(3,4)]*m
        for bits in product((0,1),repeat=m*m):
            unsafe=oracle_truth(m,bits)==2*m
            cert=certificate(m,bits)
            assert len(cert)==m and eval_cert(m,bits,cert)==(unsafe,not unsafe)
            assert all(eval_cert(m,bits,cert[:j]+cert[j+1:])==(False,False) for j in range(m))
            arithmetic+=1
    d=[depth((m,)*m) for m in range(1,8)]
    assert d==[m*m for m in range(1,8)]
    randomness=[]
    for m in range(1,6):
        # Row order probability depends only on counts; sorted counts suffice.
        from itertools import combinations_with_replacement
        best=max(expected_cost(m,c) for c in combinations_with_replacement(range(m+1),m))
        assert best==Q(m*(m+1),2)
        randomness.append(int(best))
    assert expected_cost(4,(1,1,1,1))==10
    print(json.dumps(dict(checked_timestamp_flag_arrays=arithmetic,
        deterministic_minimax_by_size=d,randomized_algorithm_worst_by_size=randomness,
        four_blocks={"selected_certificate":4,"deterministic_minimax":16,"randomized_worst_expected":10}),indent=2))


if __name__=='__main__':
    main()
