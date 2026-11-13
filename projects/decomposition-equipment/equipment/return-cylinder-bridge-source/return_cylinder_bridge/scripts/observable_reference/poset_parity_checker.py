"""Exact role-XOR certification on finite posets. Pure Python, no dependencies.
Jobs are 0..n-1; edges give strict precedence (closure not required).
Payload bit b[k] belongs to rank k (Python zero indexing).
"""
from itertools import combinations, permutations, product
import json


def closure(n, edges):
    succ = [set() for _ in range(n)]
    for i, j in edges:
        if not 0 <= i < n or not 0 <= j < n:
            raise ValueError('job out of range')
        succ[i].add(j)
    for k in range(n):
        for i in range(n):
            if k in succ[i]:
                succ[i] |= succ[k]
    if any(i in succ[i] for i in range(n)):
        raise ValueError('not a poset: cycle')
    pred = [{i for i in range(n) if j in succ[i]} for j in range(n)]
    return pred, succ


def topo(subset, pred):
    left = set(subset)
    out = []
    while left:
        ready = sorted(i for i in left if not pred[i] & left)
        if not ready:
            raise ValueError('cycle')
        i = ready[0]
        out.append(i)
        left.remove(i)
    return out


def parity(order, roles, bits):
    out = {r: 0 for r in roles}
    for k, i in enumerate(order):
        out[roles[i]] ^= bits[k]
    return out


def witness_orders(n, pred, succ, i, j, k):
    """k is zero-indexed first position of adjacent i,j."""
    d = pred[i] | pred[j]
    u = succ[i] | succ[j]
    a = set(range(n)) - u - {i, j}
    prefix_order = topo(d, pred) + topo(a - d, pred)
    prefix = prefix_order[:k]
    tail = topo(set(range(n)) - set(prefix) - {i, j}, pred)
    return prefix + [i, j] + tail, prefix + [j, i] + tail


def certify(n, edges, roles, bits, required=None):
    """CERTIFIED = all extensions attain required (or common reference) parity.
    A NONINVARIANT answer has two valid extensions of different role parity;
    TARGET_MISMATCH has a valid extension violating the prescribed target.
    """
    if len(roles) != n or len(bits) != n or any(b not in (0, 1) for b in bits):
        raise ValueError('invalid lengths or nonbinary payload')
    pred, succ = closure(n, edges)
    reference = topo(range(n), pred)
    base = parity(reference, roles, bits)
    for i, j in combinations(range(n), 2):
        if roles[i] == roles[j] or i in pred[j] or j in pred[i]:
            continue
        lo = len(pred[i] | pred[j])
        hi = n - len(succ[i] | succ[j]) - 2
        for k in range(lo, hi + 1):
            if bits[k] != bits[k + 1]:
                p, q = witness_orders(n, pred, succ, i, j, k)
                return dict(status='NONINVARIANT', pair=[i, j], rank_1based=k+1,
                            orders=[p, q], parities=[parity(p, roles, bits), parity(q, roles, bits)])
    if required is not None and base != required:
        return dict(status='TARGET_MISMATCH', order=reference, parity=base)
    return dict(status='CERTIFIED', order=reference, parity=base)


def verify_failure(n, edges, roles, bits, cert, required=None):
    """Independent witness verifier: checks original edges, not interval theorem."""
    def valid(order):
        if sorted(order) != list(range(n)):
            return False
        pos = {j:k for k,j in enumerate(order)}
        return all(pos[i] < pos[j] for i,j in edges)
    def xor_direct(order):
        return {r: sum(bits[k] for k,j in enumerate(order) if roles[j] == r) % 2
                for r in set(roles)}
    if cert['status'] == 'NONINVARIANT':
        p, q = cert['orders']
        return valid(p) and valid(q) and xor_direct(p) != xor_direct(q)
    if cert['status'] == 'TARGET_MISMATCH':
        p = cert['order']
        return required is not None and valid(p) and xor_direct(p) != required
    return False


def all_natural_posets(n):
    pairs = list(combinations(range(n), 2))
    seen = set()
    for mask in range(1 << len(pairs)):
        edges = [p for k,p in enumerate(pairs) if mask >> k & 1]
        _, succ = closure(n, edges)
        key = tuple(tuple(sorted(s)) for s in succ)
        if key not in seen:
            seen.add(key)
            yield [(i,j) for i,s in enumerate(succ) for j in s]


def exhaustive(max_n=5):
    from poset_parity_verifier import verify
    counts = []
    gap = None
    for n in range(1, max_n+1):
        count = cases = failures = intervals = relabeled = 0
        perms = list(permutations(range(n)))
        for edges in all_natural_posets(n):
            count += 1
            exts = [p for p in perms if all(p.index(i) < p.index(j) for i,j in edges)]
            pred, succ = closure(n, edges)
            for i,j in combinations(range(n), 2):
                if i in pred[j] or j in pred[i]: continue
                observed = {k for p in exts for k in range(n-1) if {p[k],p[k+1]} == {i,j}}
                expected = set(range(len(pred[i]|pred[j]), n-len(succ[i]|succ[j])-1))
                assert observed == expected
                for k in expected:
                    a,b = witness_orders(n,pred,succ,i,j,k)
                    assert tuple(a) in exts and tuple(b) in exts
                    intervals += 1
            allowed = [{p[k] for p in exts} for k in range(n)]
            matchings = [p for p in perms if all(p[k] in allowed[k] for k in range(n))]
            for roles in product(range(2), repeat=n):
                for bits in product(range(2), repeat=n):
                    cases += 1
                    values = {tuple(parity(p,roles,bits).items()) for p in exts}
                    result = certify(n,edges,roles,bits)
                    assert verify(n,edges,roles,bits,result)
                    invariant = len(values)==1
                    assert (result['status']=='CERTIFIED') == invariant
                    if not invariant:
                        assert verify_failure(n,edges,roles,bits,result)
                        failures += 1
                    if gap is None and invariant:
                        base = parity(exts[0],roles,bits)
                        bad = next((p for p in matchings if parity(p,roles,bits)!=base),None)
                        if bad is not None:
                            gap = dict(n=n,edges=edges,roles=roles,bits=bits,
                                       extensions=exts,rank_allowed=allowed,
                                       spurious_matching=bad,common_parity=base,
                                       spurious_parity=parity(bad,roles,bits))
                            gap['rank_allowed'] = [sorted(s) for s in allowed]
                            print('GAP',json.dumps(gap),flush=True)
            # Relabel every poset in reverse order and test all bits with distinct roles.
            mapping = list(reversed(range(n)))
            re = [(mapping[i],mapping[j]) for i,j in edges]
            roles = tuple(range(n))
            rexts = [tuple(mapping[i] for i in p) for p in exts]
            for bits in product(range(2),repeat=n):
                res = certify(n,re,roles,bits)
                assert verify(n,re,roles,bits,res)
                vals = {tuple(sorted(parity(p,roles,bits).items())) for p in rexts}
                assert (res['status']=='CERTIFIED') == (len(vals)==1)
                if res['status']!='CERTIFIED': assert verify_failure(n,re,roles,bits,res)
                relabeled += 1
        row=dict(n=n,posets=count,binary_role_payload_cases=cases,
                 verified_noninvariance_witnesses=failures,
                 verified_adjacent_rank_constructions=intervals,
                 relabeled_distinct_role_cases=relabeled)
        counts.append(row)
        print(json.dumps(row),flush=True)
    # Explicit target and input rejection tests.
    assert certify(2,[(0,1)],['a','b'],[0,1],{'a':0,'b':1})['status']=='CERTIFIED'
    c=certify(2,[(0,1)],['a','b'],[0,1],{'a':1,'b':0})
    assert verify_failure(2,[(0,1)],['a','b'],[0,1],c,{'a':1,'b':0})
    try: certify(2,[(0,1),(1,0)],['a','b'],[0,1])
    except ValueError: pass
    else: raise AssertionError('cycle accepted')
    return dict(results=counts,rank_matching_gap=gap,status='ALL TESTS PASSED')

if __name__=='__main__':
    import pathlib
    result=exhaustive()
    path=pathlib.Path(__file__).with_name('poset_parity_test_results.json')
    path.write_text(json.dumps(result,indent=2)+'\n')
    print(result['status'],flush=True)
