#!/usr/bin/env python3
"""Exact finite checks for evolving test-generation and wiring.
No third-party modules; column bitmasks, total deterministic native maps.
"""
from itertools import product, combinations
from collections import deque
import json


def inverse(f, c):
    return sum(1 << x for x, y in enumerate(f) if c >> y & 1)


def generated(n, seeds, ops):
    """Least preimage-closed family and a word witnessing every column.
    Stored word is native execution order, with final seed column.
    """
    witness = {c: ((), c) for c in seeds}
    queue = deque(witness)
    while queue:
        c = queue.popleft()
        suffix, seed = witness[c]
        for label, f in ops.items():
            d = inverse(f, c)
            if d not in witness:
                witness[d] = ((label,) + suffix, seed)
                queue.append(d)
    return set(witness), witness


def meet_hull(n, cols):
    out = {(1 << n) - 1}
    for c in cols:
        out |= {a & c for a in list(out)}
    return out


def closure(n, cols, a):
    out = (1 << n) - 1
    for c in cols:
        if a & ~c == 0:
            out &= c
    return out


def partition(n, cols):
    cs = sorted(cols)
    blocks = {}
    for x in range(n):
        sig = tuple(bool(c >> x & 1) for c in cs)
        blocks.setdefault(sig, []).append(x)
    return sorted(blocks.values())


def faces(n, cols):
    return {a for a in range(1, 1 << n) if any(a & ~c == 0 for c in cols)}


def rank_f2(vectors):
    basis = {}
    for v in vectors:
        while v:
            i = v.bit_length() - 1
            if i in basis:
                v ^= basis[i]
            else:
                basis[i] = v
                break
    return len(basis)


def betti(n, cols):
    fs = faces(n, cols)
    by_dim = [[s for s in sorted(fs) if s.bit_count() == k + 1] for k in range(n)]
    ranks = [0] * (n + 1)
    for k in range(1, n):
        index = {s: i for i, s in enumerate(by_dim[k-1])}
        vectors = []
        for s in by_dim[k]:
            boundary = 0
            for v in range(n):
                if s >> v & 1:
                    boundary ^= 1 << index[s ^ (1 << v)]
            vectors.append(boundary)
        ranks[k] = rank_f2(vectors)
    return [len(by_dim[k]) - ranks[k] - ranks[k+1] for k in range(n)]


def view(n, cols):
    return dict(columns=sorted(cols), partition=partition(n,cols),
                extents=sorted(meet_hull(n,cols)),
                faces=sorted(faces(n,cols)), betti_mod2=betti(n,cols))


def wiring_example():
    # Native states 00, 01, 10, 11; cylinder columns x=0,x=1,y=0,y=1.
    n=4
    seeds={0b0011,0b1100,0b0101,0b1010}
    cnot=(0,1,3,2)
    reset_y=(0,0,2,2)
    f1,w1=generated(n,seeds,{'CNOT':cnot})
    f2,w2=generated(n,seeds,{'CNOT':cnot,'reset_y':reset_y})
    assert f1 == {3,12,5,10,6,9}
    assert f2 == f1 | {0,15}
    assert len(meet_hull(n,seeds))==10
    assert len(meet_hull(n,f1))==12
    assert meet_hull(n,f1)==meet_hull(n,f2)
    assert partition(n,seeds)==partition(n,f1)==partition(n,f2)==[[0],[1],[2],[3]]
    assert betti(n,seeds)==[1,1,0,0]
    assert betti(n,f1)==[1,3,0,0]
    assert betti(n,f2)==[1,0,0,0]
    # A generator-compatible complete join map on the old concept lattice
    # is impossible: {00,11} is old-closed to all four states, but images
    # {00,10} are a proper y=0 column.
    a=0b1001
    image=lambda f,c: sum(1 << y for y in set(f[x] for x in range(n) if c>>x&1))
    assert closure(n,seeds,a)==15
    assert closure(n,seeds,image(cnot,a))==5
    assert image(cnot,closure(n,seeds,a)) & ~closure(n,seeds,image(cnot,a))
    return {'states':['00','01','10','11'],'local':view(n,seeds),
            'CNOT':view(n,f1),'CNOT_and_reset':view(n,f2),
            'CNOT_native_words':w1,'combined_native_words':w2}


def find_noncommutation():
    # Smallest tested carriers; a,b are separate changes of operations.
    for n in range(2,5):
        funcs=list(product(range(n),repeat=n))
        for a in funcs:
            for b in funcs:
                for seed in range(1,1<<n):
                    base={seed}
                    fb,_=generated(n,base,{'b':b})
                    fab,_=generated(n,fb,{'a':a})
                    full,w=generated(n,base,{'a':a,'b':b})
                    # Require actual predictive difference, not just syntax.
                    if partition(n,fab)!=partition(n,full):
                        lost=sorted(full-fab)
                        return dict(n=n,a=a,b=b,seed=seed,
                                    first_b_then_a=view(n,fab),
                                    full=view(n,full),missing_witnesses={c:w[c] for c in lost})
    raise AssertionError('No example')


def check_refinement_and_lifts(max_n=3):
    totals={'contexts':0,'operation_stable_contexts':0,'strict_growth_cases':0,
            'projection_action_checks':0,'exactness_checks':0}
    for n in range(1,max_n+1):
        allcols=list(range(1<<n))
        # All contexts as families of distinct columns.
        for bits in range(1<<len(allcols)):
            seeds={c for c in allcols if bits>>c&1}
            m0=meet_hull(n,seeds)
            for f in product(range(n),repeat=n):
                full,_=generated(n,seeds,{'f':f})
                m1=meet_hull(n,full)
                totals['contexts']+=1
                totals['strict_growth_cases']+=int(m0!=m1)
                assert m0<=m1
                # All added columns old-closed iff no FCA growth.
                stable=all(inverse(f,c) in m0 for c in m0)
                assert (m0==m1)==stable
                # Coarsest stable row partition: Q does not change iff f
                # respects initial row equivalence.
                p0=partition(n,seeds)
                block={x:i for i,b in enumerate(p0) for x in b}
                congruent=all(len({block[f[x]] for x in b})<=1 for b in p0)
                assert (p0==partition(n,full))==congruent
                # Support exactness iff each one-step column is old-covered.
                cover=all(any(inverse(f,c)&~d==0 for d in seeds) for c in seeds)
                # Empty family special-case: both are empty complexes and
                # criterion is vacuous. Empty column coverage has no effect.
                assert (faces(n,seeds)==faces(n,full))==cover
                totals['exactness_checks']+=3
                if stable:
                    totals['operation_stable_contexts']+=1
                    # Arbitrarily add one new observation, saturate, and
                    # check old/new operation left adjoints commute with
                    # rho=c_old on all new extents.
                    image=lambda c: sum(1<<y for y in set(f[x] for x in range(n) if c>>x&1))
                    for extra in allcols:
                        refined,_=generated(n,seeds|{extra},{'f':f})
                        for A in meet_hull(n,refined):
                            lhs=closure(n,seeds,closure(n,refined,image(A)))
                            rhs=closure(n,seeds,image(closure(n,seeds,A)))
                            assert lhs==rhs
                            totals['projection_action_checks']+=1
    return totals


def check_support_issue():
    # Empty preimages never add a nonempty face. If there is at least one
    # old column, empty columns are covered automatically. With no old
    # columns, preimage closure remains empty, so exactness still holds.
    return 'Empty column checked in all families, including empty family.'


def extra_regression_witnesses():
    # Existing operations must act on NEW tests too. Old empty test family
    # is stable under swap; adding {0} requires {1} as well.
    swap=(1,0)
    grown,w=generated(2,{1},{'old_swap':swap})
    assert grown=={1,2}
    assert meet_hull(2,grown)=={0,1,2,3}
    # Reachable automata refinement with native new letter b.
    a=(0,0,0); b=(0,0,1)
    old,_=generated(3,{1},{'a':a})
    new,wnew=generated(3,{1},{'a':a,'b':b})
    assert old=={1,7} and new=={1,3,7}
    assert partition(3,old)==[[0],[1,2]]
    assert partition(3,new)==[[0],[1],[2]]
    assert faces(3,old)==faces(3,new)
    # Action-domain growth without any full lattice or row change.
    const1=(1,1)
    oldf={0,1}; newf={0,1,3}
    assert generated(2,oldf,{'p':const1})[0]==oldf
    assert generated(2,newf,{'p':const1})[0]==newf
    assert meet_hull(2,oldf)==meet_hull(2,newf)
    assert partition(2,oldf)==partition(2,newf)
    image=lambda f,c: sum(1<<y for y in set(f[x] for x in range(len(f)) if c>>x&1))
    olddom={u for u in faces(2,oldf) if image(const1,u) in faces(2,oldf)}
    newdom={u for u in faces(2,newf) if image(const1,u) in faces(2,newf)}
    assert olddom==set() and newdom=={1,2,3}
    return {'old_operation_new_seed':view(2,grown),
            'automata_old':view(3,old),'automata_new':view(3,new),
            'automata_native_words':wnew,
            'action_domain_growth':{'old':sorted(olddom),'new':sorted(newdom)}}


if __name__=='__main__':
    result={'wiring':wiring_example(),'noncommuting_changes':find_noncommutation(),
            'exhaustive':check_refinement_and_lifts(),'support_conventions':check_support_issue(),
            'extra_regressions':extra_regression_witnesses()}
    print(json.dumps(result,indent=2))
