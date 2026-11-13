#!/usr/bin/env python3
"""Standard-library exhaustive witnesses. No external mathematical libraries."""
from itertools import product, combinations
import json
from pathlib import Path

def powerset(xs):
    xs=tuple(xs)
    return [frozenset(xs[i] for i in range(len(xs)) if mask>>i&1)
            for mask in range(1<<len(xs))]

def closure(A,H,columns):
    common=[C for C in columns if A<=C]
    return frozenset(h for h in H if all(h in C for C in common))

def closed_sets(H,columns):
    return [A for A in powerset(H) if closure(A,H,columns)==A]

def quotient(H,tests):
    blocks={}
    for h in H:
        blocks.setdefault(tuple(test(h) for test in tests),set()).add(h)
    return list(map(frozenset,blocks.values()))

def kernel_refines(Q,R):
    return all(any(a<=b for b in R) for a in Q)

def faces(H,columns):
    return {A for A in powerset(H) if not A or any(A<=C for C in columns)}

def gf2_rank(vectors):
    pivots={}
    for x in vectors:
        while x:
            p=x.bit_length()-1
            if p not in pivots:
                pivots[p]=x;break
            x^=pivots[p]
    return len(pivots)

def betti(K):
    if not any(K): return []
    dim=max(map(len,K))-1
    bases=[sorted((tuple(sorted(A)) for A in K if len(A)==k+1)) for k in range(dim+1)]
    ranks=[0]
    for k in range(1,dim+1):
        idx={a:i for i,a in enumerate(bases[k-1])}
        columns=[]
        for a in bases[k]:
            v=0
            for j in range(len(a)):
                v^=1<<idx[a[:j]+a[j+1:]]
            columns.append(v)
        ranks.append(gf2_rank(columns))
    ranks.append(0)
    return [len(bases[k])-ranks[k]-ranks[k+1] for k in range(dim+1)]

out={}
# 1. Incomparable diagnostics do not induce a state-profile map either way.
H=list(product((0,1),repeat=2))
Qx=quotient(H,[lambda h:h[0]])
Qy=quotient(H,[lambda h:h[1]])
Qxy=quotient(H,[lambda h:h[0],lambda h:h[1]])
assert not kernel_refines(Qx,Qy) and not kernel_refines(Qy,Qx)
assert kernel_refines(Qxy,Qx) and kernel_refines(Qxy,Qy)
out['incomparable_interfaces']={'x_blocks':len(Qx),'y_blocks':len(Qy),'joint_blocks':len(Qxy),'state_compatible_map_either_way':False}

# 2. Mixed change: evidence restriction (right adjoint) and test forgetting
# (left adjoint) fail Beck--Chevalley even with all supports nonempty.
H=frozenset('abc'); retained=frozenset('ab')
old=[frozenset('a'),H]
new=old+[frozenset('ac')]
A=frozenset('ac')
assert closure(A,H,new)==A
left=closure(A,H,old)&retained
right=closure(A&retained,retained,[C&retained for C in old])
assert left==retained and right==frozenset('a') and right<left
for B,cols in [(A,new),(closure(A,H,old),old),(left,[C&retained for C in old]),(right,[C&retained for C in old])]:
    assert B and any(B<=C for C in cols)
out['mixed_adjoint_square']={'H':sorted(H),'retained':sorted(retained),'old_columns':[sorted(C) for C in old],'new_column':['a','c'],'A':sorted(A),'forget_then_restrict':sorted(left),'restrict_then_forget':sorted(right),'all_extents_supported':True}

# Exhaustive check of lax inequality for every 3x3 Boolean table, every
# retained object subset, and every fine closed extent. Old tests are first two.
lax_cases=0;strict_cases=0;dense_cases=0
H=frozenset(range(3))
for mask in range(1<<9):
    new=[frozenset(h for h in H if mask>>(h*3+e)&1) for e in range(3)]
    old=new[:2]
    row=lambda h:tuple(h in C for C in new)
    for retained in powerset(H):
        dense=all(any(row(h)==row(k) for k in retained) for h in H)
        for A in closed_sets(H,new):
            left=closure(A,H,old)&retained
            right=closure(A&retained,retained,[C&retained for C in old])
            assert right<=left
            lax_cases+=1;strict_cases+=right!=left
            if dense:
                assert right==left;dense_cases+=1
out['mixed_adjoint_exhaustive']={'Boolean_tables':512,'cases':lax_cases,'strict_cases':strict_cases,'row_dense_cases_all_exact':dense_cases}

# 3. Covariant enrichment induces a nerve inclusion but quotient forgetful map
# points backwards. Redundant tautology retains concept lattice and quotient,
# changes topology. This is a recheck of the prior corpus, NOT a new result.
H=frozenset(range(3)); cols=[H-{i} for i in H]
cols_plus=cols+[H]
assert closed_sets(H,cols)==closed_sets(H,cols_plus)
assert betti(faces(H,cols))==[1,1]
assert betti(faces(H,cols_plus))==[1,0,0]
out['prior_tautology_counterexample']={'same_closed_extents':True,'before_betti':betti(faces(H,cols)),'after_betti':betti(faces(H,cols_plus))}

# 4. Independently realizable pairwise interfaces need not have joint witnesses.
D=(0,1); neq={(0,1),(1,0)}
pairs=[('x','y'),('y','z'),('z','x')]
def solutions(edges,rels):
    return [dict(zip('xyz',v)) for v in product(D,repeat=3)
            if all((v['xyz'.index(a)],v['xyz'.index(b)]) in r for (a,b),r in zip(edges,rels))]
assert all({a for a,b in neq}==set(D) and {b for a,b in neq}==set(D) for _ in pairs)
assert not solutions(pairs,[neq]*3)
pair_solutions=[len(solutions([pairs[j] for j in range(3) if j!=i],[neq]*2)) for i in range(3)]
assert pair_solutions==[2,2,2]
out['cyclic_joint_witness_failure']={'each_constraint_biprojection_surjective':True,'each_two_constraint_network_solutions':pair_solutions,'three_constraint_solutions':0}

# All binary 3-variable tree networks with nonempty domains and surjective
# restricted edge relations have a solution extending every value at every node.
domains=[frozenset((0,)),frozenset((1,)),frozenset((0,1))]
tree_cases=0
for Ds in product(domains,repeat=3):
    eligible=[]
    for a,b in [(0,1),(1,2)]:
        rs=[]
        for r in powerset(product(Ds[a],Ds[b])):
            if {x for x,y in r}==set(Ds[a]) and {y for x,y in r}==set(Ds[b]):rs.append(r)
        eligible.append(rs)
    for r01,r12 in product(*eligible):
        sols=[v for v in product(*Ds) if (v[0],v[1]) in r01 and (v[1],v[2]) in r12]
        assert sols
        assert all({v[i] for v in sols}==set(Ds[i]) for i in range(3))
        tree_cases+=1
out['tree_positive_class_exhaustive']={'domain_choices':27,'admitted_networks':tree_cases,'all_values_extend':True}

# 5. Old local characterizations need not remain sound after a joint new test.
H=list(product(D,repeat=2)); oldQ=quotient(H,[]); parityQ=quotient(H,[lambda h:h[0]^h[1]])
assert len(oldQ)==1 and len(parityQ)==2 and not kernel_refines(oldQ,parityQ)
out['new_joint_test_unsoundness']={'old_component_product_blocks':1,'new_joint_parity_blocks':2,'factor_from_old_product':False}

# 6. Available as separate experiments is not available as one identification
# policy: one consumable token, a 2-bit hidden state, each query consumes it.
worlds=list(product(D,repeat=2))
leaf_counts=[]
for chosen_query in (0,1):
    leaves=[[w for w in worlds if w[chosen_query]==answer] for answer in D]
    assert all(len(leaf)==2 for leaf in leaves)
    leaf_counts.append([len(leaf) for leaf in leaves])
assert len(quotient(worlds,[lambda h:h[0],lambda h:h[1]]))==4
out['one_token_identification_gap']={'semantic_row_classes':4,'remaining_worlds_per_leaf_for_each_first_query':leaf_counts,'sure_single_run_identification':False}

# 7. Evidence restriction strengthens old implications; naming new tests on
# fixed H does not change the truth of old implications.
H=frozenset('ab'); old=[frozenset('ab'),frozenset('a')]
assert not old[0]<=old[1]
retained=frozenset('a')
assert old[0]&retained<=old[1]&retained
out['evidence_vs_language']={'p_implies_q_on_original_evidence':False,'p_implies_q_after_evidence_restriction':True,'adding_unrelated_columns_cannot_change_this_old_implication':True}

# 8. A newly named readout need not be continuation-closed.
H=frozenset('abc'); p=frozenset('c'); u={'a':'c','b':'b','c':'c'}
readout_Q=quotient(H,[lambda h:h in p])
preimage=frozenset(h for h in H if u[h] in p)
completed_Q=quotient(H,[lambda h:h in p,lambda h:h in preimage])
assert len(readout_Q)==2 and len(completed_Q)==3
assert ('a' in p)==('b' in p) and (u['a'] in p)!=(u['b'] in p)
out['readout_needs_continuation_closure']={'readout_classes':2,'continuation_closed_classes':3,'new_preimage_column':sorted(preimage)}

# 9. Nonempty conjunction closure preserves the witness nerve; disjunction
# closure makes it the full simplex on the live carrier. Check all 3x3 tables.
H=frozenset(range(3)); language_cases=0
for mask in range(1<<9):
    cols=[frozenset(h for h in H if mask>>(h*3+e)&1) for e in range(3)]
    intersections=[];unions=[]
    for idxs in powerset(range(3)):
        if not idxs:continue
        intersections.append(frozenset.intersection(*(cols[i] for i in idxs)))
        unions.append(frozenset.union(*(cols[i] for i in idxs)))
    assert faces(H,cols)==faces(H,intersections)
    live=frozenset.union(*cols)
    assert faces(H,unions)==set(powerset(live))
    language_cases+=1
out['logical_language_topology']={'tables_checked':language_cases,'nonempty_conjunction_preserves_nerve':True,'disjunction_closure_full_simplex_on_live_objects':True}

# 10. Fixed-degree H1 can change under one bit at normalized Hamming 1/n^2,
# with all rows and columns live. Pad the 3x3 witness by identity blocks.
stability=[]
for n in range(3,9):
    H=frozenset(range(n))
    cols=[frozenset(set(range(3))-{e}) if e<3 else frozenset((e,)) for e in range(n)]
    changed=[C | {0} if e==0 else C for e,C in enumerate(cols)]
    before=betti(faces(H,cols));after=betti(faces(H,changed))
    assert before[1]==1 and after[1]==0
    assert all(C for C in cols) and all(any(h in C for C in cols) for h in H)
    assert sum(len(a^b) for a,b in zip(cols,changed))==1
    stability.append({'n':n,'normalized_Hamming':1/(n*n),'H1_before':1,'H1_after':0})
out['fixed_degree_topology_instability']=stability

path=Path(__file__).with_name('finite_check_results.json')
path.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
print('All assertions passed. Results written to '+str(path))
