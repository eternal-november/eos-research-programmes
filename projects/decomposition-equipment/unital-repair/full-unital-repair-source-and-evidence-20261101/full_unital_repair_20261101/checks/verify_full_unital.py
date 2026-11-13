#!/usr/bin/env python3
"""Independent finite checks for the frozen full-unital elementary relation.

Builds actual transformation monoids; never imports author implementations.
The exact scalar-stage formulas are *finite checked conjectures here*, not a
proof for untested k. The three typed profiles are deliberately NOT advertised
as an enumeration of all old graphs/profiles. Runtime checks survive python -O.
"""
from collections import defaultdict
from hashlib import sha256
from itertools import product
from pathlib import Path
import argparse
import json

HERE = Path(__file__).resolve().parent
SHARED = HERE.parent.parent

class VerificationFailure(RuntimeError):
    pass

def require(condition, message):
    if not condition:
        raise VerificationFailure(message)

def compose(f, g):
    return tuple(f[i] for i in g)

def canonical(keys):
    mapping = {}
    return tuple(mapping.setdefault(key, len(mapping)) for key in keys)

def count(partition):
    return len(set(partition))

def actual_monoid(k):
    identity = tuple(range(k))
    a = (k - 1, 1) + tuple(range(1, k - 1))
    b = (1, 2) + (1,) * (k - 2)
    states, work = {identity}, [identity]
    while work:
        x = work.pop()
        for generator in (a, b):
            y = compose(generator, x)
            if y not in states:
                states.add(y)
                work.append(y)
    states = tuple(sorted(states))
    index = {x: i for i, x in enumerate(states)}
    table = tuple(tuple(index[compose(x, y)] for y in states) for x in states)
    labels, power = {}, identity
    for i in range(k):
        labels[index[power]] = ('A', i)
        labels[index[compose(b, power)]] = ('B', i)
        if i < k - 2:
            labels[index[compose(compose(b, b), power)]] = ('D', i)
        power = compose(a, power)
    require(len(states) == 3 * k - 2, f'wrong generated order k={k}')
    require(len(labels) == len(states), f'normal forms not exhaustive k={k}')
    unit = index[identity]
    H = {unit, index[b], index[compose(b, b)]}
    require(all(table[unit][x] == x == table[x][unit] for x in range(len(states))), 'unit')
    require(all((table[x][y] in H) == (x in H and y in H)
                for x, y in product(range(len(states)), repeat=2)), 'H multiplication')
    return states, table, unit, H, labels

def cut_step(table, unit, partition, include_unit=True):
    records = [set() for _ in partition]
    for a, row in enumerate(table):
        for b, source in enumerate(row):
            records[source].add((partition[a], partition[b]))
    return canonical((partition[x], x == unit if include_unit else None,
                      frozenset(records[x])) for x in range(len(partition)))

def context_step(table, partition):
    return canonical((partition[x], tuple(partition[y] for y in table[x]),
                      tuple(partition[row[x]] for row in table))
                     for x in range(len(table)))

def saturate(seed, step):
    history = [seed]
    while True:
        refined = step(history[-1])
        if refined == history[-1]:
            return history
        require(count(refined) > count(history[-1]), 'refinement did not strictly grow')
        history.append(refined)

def expected_scalar(k, labels, stage):
    t = k - 1
    def key(label):
        row, i = label
        if stage == 0:
            return ('H', i == 0)
        if stage == 1:
            if row == 'A' and i == 0: return ('e',)
            if i == 0: return ('Hnonunit',)
            return ('index1' if i == 1 else 'tail',)
        if stage == 2:
            if i == t: return ('constants',)
            if i == t - 1: return ('BDtail_and_penultimate_A',)
            if i < 4: return ('A' if row == 'A' else 'BD', i)
            return ('Atail' if row == 'A' else 'BDtail_and_penultimate_A',)
        if i >= t - 1: return (row, i)
        family = 'A' if row == 'A' else 'BD'
        return (family, i) if i < 2 ** stage else (family, 'tail')
    return canonical(key(labels[i]) for i in range(len(labels)))

def scalar_case(k):
    states, table, unit, H, labels = actual_monoid(k)
    seed = canonical(x in H for x in range(len(states)))
    old = saturate(seed, lambda p: cut_step(table, unit, p, False))
    unital = saturate(seed, lambda p: cut_step(table, unit, p))
    top = saturate((0,) * len(states), lambda p: cut_step(table, unit, p))
    expected_rounds = max(3, (k - 4).bit_length())
    require(len(unital) - 1 == expected_rounds, f'unital rounds k={k}')
    for r, partition in enumerate(unital):
        require(partition == expected_scalar(k, labels, r), f'complete stage shape k={k},r={r}')
        expected_count = 2 if r == 0 else 4 if r == 1 else min(2*k-2,11) if r == 2 else min(2*k,2**(r+1)+6)
        require(count(partition) == expected_count, f'stage counts k={k},r={r}')
    require(count(old[-1]) == k, 'binary-only negative control')
    require(top[-1] == unital[-1], f'top stable partition k={k}')
    require(context_step(table, seed) == seed, 'P0 should be a congruence')
    s_after_c = saturate(unital[-1], lambda p: context_step(table,p))
    require(count(s_after_c[-1]) == len(states), 'S(Cu(P0)) must be discrete')
    nameindex = {label: x for x, label in labels.items()}
    b, d, ab = nameindex['B', 0], nameindex['D', 0], nameindex['A', k-1]
    require(seed[b] == seed[d] and unital[-1][b] == unital[-1][d], 'mixed-only pair pure theories')
    require(unital[-1][table[b][ab]] != unital[-1][table[d][ab]], 'mixed-only context distinguished')
    return {'k':k, 'order':len(states), 'binary_counts':list(map(count,old)),
            'unital_counts':list(map(count,unital)), 'top_unital_counts':list(map(count,top)),
            'unital_rounds':len(unital)-1, 'S_after_C_counts':list(map(count,s_after_c)),
            'mixed_only_pair':['B0','D0'], 'mixed_context':'right A_(k-1)=right ab'}

def product_table(table):
    n = len(table)
    return tuple(tuple(table[a][c]*n + table[b][d]
                       for c,d in product(range(n),repeat=2))
                 for a,b in product(range(n),repeat=2))

def swap_step(partition,n):
    return canonical((partition[a*n+b],partition[b*n+a]) for a,b in product(range(n),repeat=2))

def product_case(k):
    states, table, unit, H, labels = actual_monoid(k)
    n = len(states)
    pairs = tuple(product(range(n), repeat=2))
    multiplication = product_table(table)
    pair_unit = unit*n + unit
    scalar = saturate(canonical(x in H for x in range(n)),lambda p:cut_step(table,unit,p))[-1]
    seed = canonical(a in H for a,b in pairs)
    C = saturate(seed,lambda p:cut_step(multiplication,pair_unit,p))
    CT = saturate(swap_step(seed,n),lambda p:cut_step(multiplication,pair_unit,p))
    TC = swap_step(C[-1],n)
    expected = canonical(('H2-nonunit',) if a in H and b in H and (a,b)!=(unit,unit)
                         else (scalar[a],scalar[b]) for a,b in pairs)
    require(C[-1] == expected, f'product complete form k={k}')
    require(CT[-1] == TC == C[-1], f'product C/T equality k={k}')
    require(count(C[-1]) == 4*k*k - 2, f'product count k={k}')
    tensor = canonical((scalar[a],scalar[b]) for a,b in pairs)
    require(C[-1] != tensor, 'tensor negative control failed')
    mixed = saturate(C[-1],lambda p:context_step(multiplication,p))
    require(count(mixed[-1]) == n*n, 'product S after C discrete')
    return {'k':k,'carrier_size':n*n,'C_counts':list(map(count,C)),
            'C_after_T_counts':list(map(count,CT)),'T_after_C_count':count(TC),
            'scalar_tensor_count':count(tensor),'S_after_C_counts':list(map(count,mixed)),
            'exception':'H^2 minus the pair unit is one block; elsewhere scalar Cu tensor classes'}

def typed_case(k,contexts):
    states, m, e, H, labels = actual_monoid(k)
    n=len(m)
    carriers=(tuple((x,) for x in range(n)),tuple((x,) for x in range(n)),tuple(product(range(n),repeat=2)))
    # I=(1), J=(2), K=(1,1), source and complete input carrier sorts.
    operations=((0,(0,0),lambda a,b:(m[a[0]][b[0]],)),
                (1,(1,1),lambda a,b:(m[a[0]][b[0]],)),
                (2,(1,2),lambda a,b:(m[a[0]][b[0]],m[a[0]][b[1]])),
                (2,(2,0,0),lambda a,b,c:(m[a[0]][b[0]],m[a[1]][c[0]])))
    indexes=tuple({x:i for i,x in enumerate(C)} for C in carriers)
    all_records=[]
    for out,ins,fn in operations:
        records=[]
        for inputs in product(*(range(len(carriers[s])) for s in ins)):
            args=[carriers[s][v] for s,v in zip(ins,inputs)]
            result=indexes[out][fn(*args)]
            records.append((result,inputs))
        all_records.append(records)
    seed=tuple(canonical(tuple(x in H for x in v) for v in C) for C in carriers)
    p=seed;history=[[count(z) for z in p]]
    while True:
        keys=[[[p[s][x], s==0 and carriers[s][x][0]==e] for x in range(len(C))] for s,C in enumerate(carriers)]
        for (out,ins,fn),records in zip(operations,all_records):
            sig=[set() for _ in carriers[out]]
            for result,args in records:
                sig[result].add(tuple(p[s][v] for s,v in zip(ins,args)))
            for x,v in enumerate(sig):keys[out][x].append(frozenset(v))
            if contexts:
                for position,s in enumerate(ins):
                    others=[j for j in range(len(ins)) if j!=position]
                    context_values={}
                    for result,args in records:
                        fixed=tuple(args[j] for j in others)
                        if fixed not in context_values:context_values[fixed]=[None]*len(carriers[s])
                        context_values[fixed][args[position]]=p[out][result]
                    for fixed,values in sorted(context_values.items()):
                        require(None not in values,'partial one-hole operation')
                        for x,v in enumerate(values):keys[s][x].append(v)
        q=tuple(canonical(tuple(K) for K in each_sort) for each_sort in keys)
        if q==p:break
        require(sum(map(count,q))>sum(map(count,p)),'typed strict refinement')
        p=q;history.append([count(z) for z in p])
    if contexts:
        require(history[-1]==[n,n,n*n],f'typed mixed not discrete k={k}')
    else:
        require(history[-1]==[2*k,k,n*n-4*(k-2)**2],f'typed C count pattern k={k}')
    return {'k':k,'contexts':contexts,'stage_counts':history,
            'record_counts':list(map(len,all_records)),
            'domain':'Three active-size templates I=(1),J=(2),K=(1,1), not all old profiles; zero tree only I.'}

def left_zero_transformations(n):
    # n distinct constant transformations plus an identity on n+1 points.
    states=tuple(tuple([i]*(n+1)) for i in range(n))+(tuple(range(n+1)),)
    ix={x:i for i,x in enumerate(states)}
    return states,tuple(tuple(ix[compose(x,y)] for y in states) for x in states),n

def mapped_factor_records(table,mapping):
    fibres=[set() for _ in table]
    for a,row in enumerate(table):
        for b,x in enumerate(row):fibres[x].add((mapping[a],mapping[b]))
    return fibres

def quotient_check(source,target,source_unit,target_unit,mapping):
    require(all(mapping[source[a][b]]==target[mapping[a]][mapping[b]]
                for a,b in product(range(len(source)),repeat=2)), 'homomorphism')
    actual=mapped_factor_records(source,mapping)
    expected=mapped_factor_records(target,tuple(range(len(target))))
    require(all(actual[x]==expected[mapping[x]] for x in range(len(source))), 'binary exact lifting')
    require(all((x==source_unit)==(mapping[x]==target_unit) for x in range(len(source))), 'unit exact lifting')

def evaluate_word(table,unit,word):
    result=unit
    for x in word:result=table[result][x]
    return result

def left_zero_tests():
    survey=[]
    for n in range(1,9):
        _,source,e=left_zero_transformations(n)
        for m in range(1,n+1):
            _,target,f=left_zero_transformations(m)
            h=tuple(i%m for i in range(n))+(m,)
            quotient_check(source,target,e,f,h)
            survey.append({'source_nonunits':n,'target_nonunits':m})
    _,s,e=left_zero_transformations(4);_,t,f=left_zero_transformations(2);h=(0,1,0,1,2)
    chain=[]
    for length in range(7):
        actual=[set() for _ in s]
        for word in product(range(5),repeat=length):actual[evaluate_word(s,e,word)].add(tuple(h[x] for x in word))
        expected=[set() for _ in t]
        for word in product(range(3),repeat=length):expected[evaluate_word(t,f,word)].add(word)
        require(all(actual[x]==expected[h[x]] for x in range(5)),f'full unital chain length {length}')
        chain.append({'vertices':length,'source_target_records':sum(map(len,actual))})
    ss,tt=product_table(s),product_table(t)
    hh=tuple(h[a]*3+h[b] for a,b in product(range(5),repeat=2))
    quotient_check(ss,tt,e*5+e,f*3+f,hh)
    seed=canonical(h[a] for a,b in product(range(5),repeat=2))
    p=seed;history=[count(p)]
    while True:
        q=swap_step(cut_step(ss,e*5+e,context_step(ss,p)),5)
        if q==p:break
        p=q;history.append(count(p))
    require(p==canonical(hh) and count(p)==9,'proper two-channel unary quotient')
    chains2=[]
    for length in range(4):
        actual=[set() for _ in ss]
        for word in product(range(25),repeat=length):actual[evaluate_word(ss,24,word)].add(tuple(hh[x] for x in word))
        expected=[set() for _ in tt]
        for word in product(range(9),repeat=length):expected[evaluate_word(tt,8,word)].add(word)
        require(all(actual[x]==expected[hh[x]] for x in range(25)),f'two-channel chain {length}')
        chains2.append({'vertices':length,'source_target_records':sum(map(len,actual))})
    # Full rank-two shared-parent negative control. Both marginals lift, no common parent does.
    source_pair=(0,2);target_record=(0,f,f)
    candidates=[]
    marginal=[]
    for x in source_pair:
        marginal.append([a for a in range(5) if h[a]==0 and s[a][e]==x])
    for a,b,c in product(range(5),repeat=3):
        if (h[a],h[b],h[c])==target_record and (s[a][b],s[a][c])==source_pair:candidates.append((a,b,c))
    require(all(marginal) and not candidates,'shared-parent negative control')
    return {'homomorphism_cases':survey,'scalar_chain_checks':chain,'twochannel_chain_checks':chains2,
            'twochannel_mixed_stage_counts':history,'twochannel_carrier':25,'twochannel_quotient':9,
            'scope':'Full unital unary/chain geometry only, not branching geometry',
            'branching_counterexample':{'source_pair':source_pair,'target_parent_children':target_record,
                                      'marginal_parent_sets':marginal,'joint_lifts':candidates}}

def negative_controls():
    # C4 -> C2: all binary records lift, but nonidentity 2 maps to identity.
    s=tuple(tuple((a+b)%4 for b in range(4)) for a in range(4))
    t=tuple(tuple((a+b)%2 for b in range(2)) for a in range(2))
    h=(0,1,0,1)
    a=mapped_factor_records(s,h);b=mapped_factor_records(t,(0,1))
    require(all(a[x]==b[h[x]] for x in range(4)),'group binary control')
    require(2!=0 and h[2]==0,'group unit counterexample')
    # Verify the checker really rejects a deliberate false proposition under -O too.
    rejected=False
    try:require(False,'intentional self-test')
    except VerificationFailure:rejected=True
    require(rejected,'guard vanished under optimization')
    return {'C4_to_C2_binary_lifts':True,'C4_to_C2_zero_tree_fails_at_source':2,
            'false_check_rejected':True,'uses_assert_statements':False}

def source_manifest():
    files=['i5_joint_repair_20261031/monoid_repair_theorem.md',
           'final_acceptance_review_20261101/unit_boundary/check_unit_boundary.py',
           'final_acceptance_review_20261101/adversarial/i5_vertex_free_control.py']
    return [{'path':str(SHARED/f),'sha256':sha256((SHARED/f).read_bytes()).hexdigest()} for f in files]

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--max-k',type=int,default=64)
    ap.add_argument('--product-max-k',type=int,default=10);ap.add_argument('--typed-max-k',type=int,default=7)
    ap.add_argument('--output',type=Path,default=HERE/'full_unital_results.json');args=ap.parse_args()
    require(args.max_k>=4 and args.product_max_k>=4 and args.typed_max_k>=4,'ranges')
    scalar=[scalar_case(k) for k in range(4,args.max_k+1)]
    products=[product_case(k) for k in range(4,args.product_max_k+1)]
    typed=[typed_case(k,contexts) for k in range(4,args.typed_max_k+1) for contexts in (False,True)]
    results={'status':'All requested finite checks passed','proof_scope':'Finite corroboration only; no all-k or all-profile inference from enumeration',
             'domain_freeze':'c_u keeps P, full ordered binary class-record set, literal unit feasibility in the SAME step; P^(0)=P0',
             'scalar':scalar,'twochannel_identity_fibre':products,'typed_active_size_templates':typed,
             'positive_unary_family':left_zero_tests(),'negative_controls':negative_controls(),
             'source_manifest':source_manifest(),'checker_sha256':sha256(Path(__file__).read_bytes()).hexdigest()}
    args.output.write_text(json.dumps(results,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':results['status'],'scalar_k':[4,args.max_k],'product_k':[4,args.product_max_k],
                      'typed_k':[4,args.typed_max_k],'output':str(args.output)},indent=2))
if __name__=='__main__':main()
