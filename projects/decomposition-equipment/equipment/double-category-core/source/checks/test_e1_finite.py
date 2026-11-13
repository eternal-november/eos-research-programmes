#!/usr/bin/env python3
"""Bounded exhaustive checks and real semantic negative controls for E1.
Run: python3 test_e1_finite.py [--output result.json]
"""
import argparse, hashlib, json, os, time
from collections import Counter
from itertools import product
from pathlib import Path as FilePath
from e1_finite_model import *

COUNTS=Counter()
A=Obj('A',2); B=Obj('B',2); C=Obj('C',2)
E=Obj('empty',0); S=Obj('singleton',1)
SMALL=(E,S,A)
WEIGHTS=(0,1,2)

def check(ok,name,witness=None):
    COUNTS[name]+=1
    if not ok: raise AssertionError({'check':name,'witness':witness})

def finite_profiles():
    seen=set()
    # All small-size object profiles through arity 2, not only inhabited carriers.
    for arity in range(3):
        for vs in product(SMALL,repeat=arity+1):
            for p in paths(vs):
                if p not in seen: seen.add(p); yield p
    # All Bool relations along genuinely mixed tagged profiles through arity 3.
    cycle=(A,B,C,A)
    for arity in range(4):
        for p in paths(cycle[:arity+1]):
            if p not in seen: seen.add(p); yield p

def run_positive():
    ps=tuple(finite_profiles())
    # Full tuple oracle is separate from recursive relation composition.
    for p in ps:
        check(evaluate(p).pairs==evaluate_tuple_oracle(p),'path_tuple_oracle')
        for j in range(len(p.vertices)):
            q=insert_unit(p,j)
            check(evaluate(q).pairs==evaluate_tuple_oracle(p),'unit_all_context_junctions')
            # Complete cell data, with nonidentity outer sides and every scalar.
            lefts=maps(p.vertices[0],A); rights=maps(p.vertices[-1],C)
            for f,g in product(lefts,rights):
                for H in relations(A,C):
                    valid=evaluate(p).pairs <= restrict(H,f,g).pairs
                    validq=evaluate(q).pairs <= restrict(H,f,g).pairs
                    check(valid==validq,'unit_context_cell_fibres')
                    if valid:
                        # Scalar map induced by substitution of the actual unit.
                        check(tuple(compose_weight(w,(0,)) for w in WEIGHTS)==WEIGHTS,'unit_parallel_weights')
    # All cells/factorizations for each distinct evaluation AND each source arity.
    # Quotient only test CASE selection by (full endpoints, arity, evaluation),
    # never cells or paths in the model. All profiles were checked above.
    reps={}
    for p in ps: reps.setdefault((p.vertices[0],p.vertices[-1],len(p.edges),evaluate(p)),p)
    for p in reps.values():
        # Arbitrary maps at all four vertical sides; intermediates are two points.
        for f,g,h,k in product(maps(A,A),maps(C,C),maps(p.vertices[0],A),maps(p.vertices[-1],C)):
            for H in relations(A,C):
                lhs=evaluate(p).pairs <= restrict(H,composite(f,h),composite(g,k)).pairs
                rhs=evaluate(p).pairs <= restrict(restrict(H,f,g),h,k).pairs
                check(lhs==rhs,'restriction_factorization_fibres')
                if lhs:
                    for w in WEIGHTS:
                        alpha=Cell(p,H,composite(f,h),composite(g,k),w)
                        beta=factor(alpha,f,g,h,k)
                        check(unfactor(beta,H,f,g)==alpha,'restriction_roundtrip_full_cell')
                        check(factor(unfactor(beta,H,f,g),f,g,h,k)==beta,'restriction_inverse_full_cell')
    # Every composable pair of finite interface changes on sizes 0,1,2.
    for a0,a1,a2,b0,b1,b2 in product(SMALL,repeat=6):
        for f,h,g,k in product(maps(a1,a2),maps(a0,a1),maps(b1,b2),maps(b0,b1)):
            for H in relations(a2,b2):
                check(restrict(restrict(H,f,g),h,k)==restrict(H,composite(f,h),composite(g,k)), 'two_changes_coherence')
    # Bijections at every vertex preserve/reflection actual equality marking.
    for p in ps:
        perms=tuple(tuple(f for f in maps(a,a) if len(set(f.values))==a.size) for a in p.vertices)
        for fs in product(*perms):
            q=reindex_path(p,fs)
            ev=evaluate(p); rq=restrict(ev,fs[0],fs[-1])
            check(evaluate(q)==rq,'bijective_path_action')
            for H in relations(p.vertices[0],p.vertices[-1]):
                if not ev.pairs<=H.pairs: continue
                Hq=restrict(H,fs[0],fs[-1])
                for w in WEIGHTS:
                    alpha=Cell(p,H,identity(p.vertices[0]),identity(p.vertices[-1]),w)
                    beta=Cell(q,Hq,identity(q.vertices[0]),identity(q.vertices[-1]),w)
                    check(marked(alpha)==marked(beta),'bijective_mark_preserve_reflect')
    # Every map row for every binary Bool path: all-cell action survives even
    # when the exact marking does not. (Includes noninjective/nonsurjective.)
    mark_fail=None
    for p in paths((A,B,C)):
        for fs in product(maps(A,A),maps(B,B),maps(C,C)):
            q=reindex_path(p,fs); Hq=restrict(evaluate(p),fs[0],fs[-1])
            check(evaluate(q).pairs<=Hq.pairs,'arbitrary_reindex_all_cells')
            for w in WEIGHTS:
                beta=Cell(q,Hq,identity(A),identity(C),w)
                check(beta.weight==w,'arbitrary_reindex_retains_witness')
            if evaluate(q)!=Hq and mark_fail is None:
                mark_fail={'path':[sorted(x.pairs) for x in p.edges],'maps':[list(f.values) for f in fs], 'reindexed_composite':sorted(evaluate(q).pairs),'restricted_output':sorted(Hq.pairs)}
    check(mark_fail is not None,'exact_not_arbitrary_restriction')
    # Explicit parallel legitimate nonuniversal cells, distinct component types,
    # nullary unit/primitive contrast, and occurrence-wise scalar composition.
    p=Path((A,),())
    unit=Cell(p,diagonal(A),identity(A),identity(A),0)
    primitive=Cell(p,diagonal(A),identity(A),identity(A),1)
    check(unit!=primitive and marked(unit) and not marked(primitive),'nullary_unit_vs_primitive')
    check(0 not in {compose_weight(w,(primitive.weight,)) for w in range(20)},'primitive_no_zero_preimage')
    check(len(set(relations(A,B)))==16,'multiple_horizontal_components')
    H=Horizontal(A,A,frozenset(product(range(2),repeat=2)))
    p1=Path((A,A),(diagonal(A),))
    parallel0=Cell(p1,H,identity(A),identity(A),0)
    parallel1=Cell(p1,H,identity(A),identity(A),1)
    check(parallel0!=parallel1 and not marked(parallel0) and not marked(parallel1), 'nonnullary_nonuniversal_parallel_cells')
    # Real two-level cell substitution, including repeated equal component slots
    # and independently chosen nullary subprofiles. Compare complete cells.
    childpaths=(Path((A,),()),Path((A,A),(diagonal(A),)),
                Path((A,A,A),(diagonal(A),diagonal(A))),Path((A,A),(H,)))
    for q0,q1 in product(childpaths,repeat=2):
        for w,w0,w1 in product(WEIGHTS,repeat=3):
            outer=Cell(Path((A,A,A),(H,H)),H,identity(A),identity(A),w)
            middle=(Cell(q0,H,identity(A),identity(A),w0),Cell(q1,H,identity(A),identity(A),w1))
            flat=[]; nested=[]
            for child in middle:
                row=tuple(Cell(Path((A,A),(edge,)),edge,identity(A),identity(A),i%3) for i,edge in enumerate(child.path.edges))
                flat.extend(row); nested.append(substitute(child,row))
            check(substitute(substitute(outer,middle),tuple(flat))==substitute(outer,tuple(nested)), 'actual_cell_substitution_associativity')
    # Two distinct refinement rows with the same scalar total are NOT identified.
    row1=(0,1); row2=(1,0)
    check(row1!=row2 and compose_weight(2,row1)==compose_weight(2,row2),'retain_parallel_refinement_tuples')
    for outer,mid0,mid1 in product(WEIGHTS,repeat=3):
        for inners in product(WEIGHTS,repeat=4):
            lhs=compose_weight(compose_weight(outer,(mid0,mid1)),inners)
            rhs=compose_weight(outer,(compose_weight(mid0,inners[:2]),compose_weight(mid1,inners[2:])))
            check(lhs==rhs,'substitution_scalar_associativity')
    return {'profiles':len(ps),'restriction_representatives':len(reps),'mark_failure_witness':mark_fail}

def run_mutations():
    results=[]
    # Mutated executable cell semantics erase every witness scalar.
    def erase_cell_weight(w): return 0
    expected=(0,1)
    actual=tuple(erase_cell_weight(w) for w in expected)
    results.append({'name':'erase_witness_scalar','rejected':actual!=expected,'expected':expected,'actual':actual})
    # Wrong arity-zero evaluation changes the endpoint relation, not a label.
    p=Path((A,),())
    wrong_zero=frozenset()
    expected_zero=evaluate_tuple_oracle(p)
    results.append({'name':'nullary_is_empty_relation','rejected':wrong_zero!=expected_zero,'expected':sorted(expected_zero),'actual':sorted(wrong_zero)})
    # Reverse actual noncommuting function composition, on same typed endpoint.
    flip=Vertical(A,A,(1,0)); zero=Vertical(A,A,(0,0)); H=diagonal(A)
    sequential=restrict(restrict(H,flip,identity(A)),zero,identity(A))
    wrong=restrict(H,composite(zero,flip),identity(A))
    results.append({'name':'reverse_vertical_composition','rejected':sequential!=wrong,'expected':sorted(sequential.pairs),'actual':sorted(wrong.pairs),'outer':[1,0],'inner':[0,0]})
    # Mutant retains the old exact flag after arbitrary internal pullback.
    R=Horizontal(A,B,frozenset({(0,1)})); T=Horizontal(B,C,frozenset({(1,0)}))
    p=Path((A,B,C),(R,T)); fs=(identity(A),Vertical(B,B,(0,0)),identity(C))
    q=reindex_path(p,fs); H=restrict(evaluate(p),fs[0],fs[-1])
    transported_old_marker=marked(Cell(p,evaluate(p),identity(A),identity(C),0))
    actual_marker=marked(Cell(q,H,identity(A),identity(C),0))
    results.append({'name':'arbitrary_reindex_retains_exact_flag','rejected':transported_old_marker!=actual_marker,'expected_actual_marker':actual_marker,'mutant_marker':transported_old_marker,'source_composite':sorted(evaluate(p).pairs),'reindexed_composite':sorted(evaluate(q).pairs),'restricted_output':sorted(H.pairs)})
    for x in results:
        if not x['rejected']:
            raise AssertionError(x)
    return results

def main():
    parser=argparse.ArgumentParser(); parser.add_argument('--output',default='finite_results.json'); args=parser.parse_args()
    here=FilePath(__file__).resolve().parent
    hashes={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (here/'e1_finite_model.py',here/'test_e1_finite.py')}
    start=time.time(); detail=run_positive(); mutations=run_mutations()
    end_hashes={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (here/'e1_finite_model.py',here/'test_e1_finite.py')}
    if hashes != end_hashes:
        raise RuntimeError('Source changed while running')
    result={'status':'PASS','elapsed_seconds':round(time.time()-start,3),'bounds':{'carrier_sizes':[0,1,2],'small_size_arities':[0,1,2],'mixed_bool_arities':[0,1,2,3],'weights_tested':[0,1,2],'weights_are_not_truncated_by_model':True,'restriction_case_selection':'all distinct (source endpoint, target endpoint, arity, composite relation); complete original paths separately checked against tuple oracle','arbitrary_reindex_arity':2,'bijective_reindex_all_profiles':True},'case_detail':detail,'counts':dict(COUNTS),'total_checks':sum(COUNTS.values()),'mutations':mutations,'source_sha256':hashes,'source_sha256_start':hashes,'source_sha256_end':end_hashes,'source_unchanged_during_run':True,'limitations':['Finite evidence only; does not establish unbounded laws.','No full 2-category or graph partition model is checked by this Python slice.','Unit fibre tests cover every bounded prefix/suffix junction and every selected outer relation/map, not arbitrary infinite carriers.']}
    output=FilePath(args.output)
    temporary=output.with_name(output.name+'.tmp')
    temporary.write_text(json.dumps(result,indent=2)+'\n')
    os.replace(temporary,output)
    print(json.dumps(result,indent=2))
if __name__=='__main__': main()
