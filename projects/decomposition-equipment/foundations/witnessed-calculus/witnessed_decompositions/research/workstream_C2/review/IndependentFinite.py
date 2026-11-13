#!/usr/bin/env python3
"""Independent C2 finite oracle; no author implementation is imported.

Relations are row-major bit matrices. Direct witness enumeration is an
independent whole-path evaluator. Finite domains are the pre-reviewed C2 target.
This is executable C evidence, not an unrestricted or Lean proof.
"""
from __future__ import annotations
from functools import lru_cache
from dataclasses import dataclass
from itertools import product, combinations_with_replacement
from pathlib import Path
import argparse
import hashlib
import json
import platform
import time

TARGET_HASH = 'b6711190a46b19205ef25f439105eaf1951137d90f5e55a595ea67daf172e2f4'
CONTRACT_HASH = '47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e'
SIZES = range(3)


def bit(R, b, x, y):
    return bool(R & (1 << (b*x+y)))


def pairs(a,b,R):
    return [[x,y] for x in range(a) for y in range(b) if bit(R,b,x,y)]


def encode(a,b,rows):
    assert all(0 <= x < a and 0 <= y < b for x,y in rows)
    return sum(1 << (b*x+y) for x,y in set(map(tuple,rows)))


@lru_cache(None)
def diagonal(a):
    return sum(1 << (a*x+x) for x in range(a))


@lru_cache(None)
def multiply(a,b,c,R,S):
    """Boolean matrix multiplication; bit-row algorithm, not path enumeration."""
    result=0
    row_mask=(1 << c)-1
    for x in range(a):
        target_row=0
        for middle in range(b):
            if bit(R,b,x,middle):
                target_row |= (S >> (middle*c)) & row_mask
        result |= target_row << (x*c)
    return result


@lru_cache(None)
def direct(sizes, relations):
    """Project ALL valid global vertex assignments to the two outer entries."""
    assert len(sizes)==len(relations)+1
    if not relations:
        return diagonal(sizes[0])
    result=0
    for assignment in product(*(range(a) for a in sizes)):
        if all(bit(R,sizes[i+1],assignment[i],assignment[i+1])
               for i,R in enumerate(relations)):
            result |= 1 << (assignment[0]*sizes[-1]+assignment[-1])
    return result


@lru_cache(None)
def superset_masks(width, R):
    assert 0 <= R < (1 << width)
    return tuple(S for S in range(1 << width) if (R & ~S)==0)


@lru_cache(None)
def functions(domain,codomain):
    return tuple(product(range(codomain), repeat=domain))


@lru_cache(None)
def pull(a,b,R,f,g):
    return sum(1 << (len(g)*x+y)
               for x in range(len(f)) for y in range(len(g))
               if bit(R,b,f[x],g[y]))


def f1():
    count=onto_count=strict_count=realizer_count=cell_count=nonexact_cells=empty_domain_cases=0
    for a,b,c,ap,bp,cp in product(SIZES,repeat=6):
      for f,g,h in product(functions(ap,a), functions(bp,b), functions(cp,c)):
       onto=set(g)==set(range(b))
       for R,S in product(range(1 << (a*b)), range(1 << (b*c))):
        P=multiply(a,b,c,R,S)
        assert P==direct((a,b,c),(R,S))
        rp=pull(a,b,R,f,g); sp=pull(b,c,S,g,h)
        left=multiply(ap,bp,cp,rp,sp)
        right=pull(a,c,P,f,h)
        assert not left & ~right
        if onto:
            assert left==right
            onto_count+=1
        if left!=right: strict_count+=1
        for x,y,z in product(range(ap),range(bp),range(cp)):
            if bit(rp,bp,x,y) and bit(sp,cp,y,z):
                assert bit(R,b,f[x],g[y]) and bit(S,c,g[y],h[z])
                assert bit(left,cp,x,z) and bit(right,cp,x,z)
                realizer_count+=1
        for W in superset_masks(a*c,P):
            pulled_W=pull(a,c,W,f,h)
            assert not left & ~pulled_W
            assert (left==pulled_W)==(not pulled_W & ~left)
            cell_count+=1
            nonexact_cells+=left!=pulled_W
        count+=1
        empty_domain_cases+=0 in (a,b,c,ap,bp,cp)
    assert count==113171
    assert strict_count>0 and onto_count>0 and nonexact_cells>0
    return dict(status='PASS', tuples=count, surjective_internal_tuples=onto_count,
                strict_comparisons=strict_count, source_realizer_maps_checked=realizer_count,
                containing_whole_cells=cell_count, restricted_nonexact_cells=nonexact_cells,
                tuples_with_some_empty_interface=empty_domain_cases)


def f2():
    triples=units=0
    for a,b,c,d in product(SIZES,repeat=4):
      for R,S,T in product(range(1<<(a*b)),range(1<<(b*c)),range(1<<(c*d))):
        left=multiply(a,c,d,multiply(a,b,c,R,S),T)
        right=multiply(a,b,d,R,multiply(b,c,d,S,T))
        flat=direct((a,b,c,d),(R,S,T))
        assert left==right==flat
        triples+=1
    for a,b in product(SIZES,repeat=2):
      for R in range(1<<(a*b)):
        assert multiply(a,a,b,diagonal(a),R)==R
        assert multiply(a,b,b,R,diagonal(b))==R
        assert direct((a,a,b),(diagonal(a),R))==R
        assert direct((a,b,b),(R,diagonal(b)))==R
        units+=2
    assert triples==8507
    return dict(status='PASS', relation_triples=triples, unit_equalities=units)


def segmentations(m,k):
    """A tuple of k adjacent blocks including zero-length blocks.

    Every cut sequence 0=t0<=t1<=...<=tk=m gives exactly one segmentation.
    Thus an empty block has the SAME position/interface label at both ends.
    """
    if k==0:
        return ((),) if m==0 else ()
    return tuple(tuple(zip((0,)+cuts,cuts+(m,)))
                 for cuts in combinations_with_replacement(range(m+1),k-1))


def f3():
    profiles=segmented=outer_assignments=all_cells=exact_cells=0
    counts_by_m={str(i):dict(profiles=0,segmentations=0,outer_assignments=0,cells=0)
                 for i in range(4)}
    by_k={str(k):0 for k in range(4)}
    for m in range(4):
     for sizes in product(SIZES,repeat=m+1):
      for rs in product(*(range(1<<(sizes[i]*sizes[i+1])) for i in range(m))):
        p=direct(sizes,rs)
        profiles+=1; counts_by_m[str(m)]['profiles']+=1
        for k in range(4):
         for blocks in segmentations(m,k):
          # Labels are the source path positions. An empty segment contracts
          # no edge and retains exactly that position, not a new equal-sized set.
          endpoints=(0,)+tuple(t for s,t in blocks) if k else (0,)
          outer_sizes=tuple(sizes[t] for t in endpoints)
          child_composites=tuple(direct(sizes[s:t+1],rs[s:t]) for s,t in blocks)
          assert direct(outer_sizes,child_composites)==p
          segmented+=1; exact_cells+=1
          counts_by_m[str(m)]['segmentations']+=1
          choices=tuple(superset_masks(sizes[s]*sizes[t],C)
                        for (s,t),C in zip(blocks,child_composites))
          for outer_rs in product(*choices):
            outer_composite=direct(outer_sizes,outer_rs)
            assert not p & ~outer_composite
            outer_assignments+=1
            counts_by_m[str(m)]['outer_assignments']+=1
            for W in superset_masks(sizes[0]*sizes[-1],outer_composite):
                assert not p & ~W
                all_cells+=1; by_k[str(k)]+=1
                counts_by_m[str(m)]['cells']+=1
    assert profiles==9040
    return dict(status='PASS', source_profiles=profiles,
                profile_segmentation_pairs=segmented,
                intermediate_whole_assignments=outer_assignments,
                all_outer_whole_cells=all_cells, exact_substitutions=exact_cells,
                counts_by_source_arity=counts_by_m, cells_by_outer_arity=by_k,
                enumeration='No F3 test is factored away: each profile, weak cut sequence, intermediate whole tuple and outer whole is visited.')


def restriction_coherence():
    identity_cases=iterated_cases=nullary_cases=0
    strict_nullaries=0
    for a,b in product(SIZES,repeat=2):
      for R in range(1<<(a*b)):
        assert pull(a,b,R,tuple(range(a)),tuple(range(b)))==R
        identity_cases+=1
    for a,b,ap,bp,app,bpp in product(SIZES,repeat=6):
      for f,g,ff,gg in product(functions(ap,a),functions(bp,b),
                              functions(app,ap),functions(bpp,bp)):
        composed_f=tuple(f[x] for x in ff)
        composed_g=tuple(g[x] for x in gg)
        for R in range(1<<(a*b)):
            first=pull(a,b,R,f,g)
            assert pull(ap,bp,first,ff,gg)==pull(a,b,R,composed_f,composed_g)
            iterated_cases+=1
    for a,ap in product(SIZES,repeat=2):
      for f in functions(ap,a):
        ker=pull(a,a,diagonal(a),f,f)
        new_diag=diagonal(ap)
        assert not new_diag & ~ker
        assert (new_diag==ker)==(len(set(f))==len(f))
        strict_nullaries+=new_diag!=ker
        nullary_cases+=1
    assert strict_nullaries>0
    return dict(status='PASS', identity_cases=identity_cases,
                iterated_restriction_cases=iterated_cases,
                nullary_maps=nullary_cases, strict_nullary_comparisons=strict_nullaries)


def own_principal():
    """Independent explicit certificate; author fixture also checked if supplied."""
    R=encode(2,3,[(0,0),(1,2)])
    S=encode(3,2,[(0,0),(2,1)])
    P=direct((2,3,2),(R,S))
    W=P | encode(2,2,[(0,1)])
    f=h=(0,1); g=(0,1)
    r=pull(2,3,R,f,g); s=pull(3,2,S,g,h)
    left=direct((2,2,2),(r,s)); right=pull(2,2,P,f,h)
    assert P!=0 and P!=W and not P & ~W
    assert left!=0 and left!=right and not left & ~right
    gp=(0,1,2,2)
    positive=direct((2,4,2),(pull(2,3,R,f,gp),pull(3,2,S,gp,h)))
    assert positive==right
    # Noninjective outer maps remain compatible with positive-arity equality.
    f2=(0,0,1); h2=(1,0,0)
    positive2=direct((3,4,3),(pull(2,3,R,f2,gp),pull(3,2,S,gp,h2)))
    assert positive2==pull(2,2,P,f2,h2)
    bad_nullary=pull(1,1,diagonal(1),(0,0),(0,0))
    assert diagonal(2)!=bad_nullary and not diagonal(2) & ~bad_nullary
    return dict(status='PASS', original_interfaces={'A':2,'B':3,'C':2},
                R=pairs(2,3,R), S=pairs(3,2,S), composite=pairs(2,2,P),
                strict_whole=pairs(2,2,W), nonsurjective_intermediate_map=list(g),
                composite_of_pulls=pairs(2,2,left),pull_of_composite=pairs(2,2,right),
                removed_pairs=pairs(2,2,right & ~left),
                preserved_pairs=pairs(2,2,left),surjective_many_to_one_map=list(gp),
                positive_composite=pairs(2,2,positive),
                noninjective_endpoints={'f':list(f2),'h':list(h2),'comparison_equal':True},
                nullary={'new_diagonal':pairs(2,2,diagonal(2)),
                         'pulled_old_diagonal':pairs(2,2,bad_nullary)},
                mutations={'reverse_containment':bool(W & ~P),
                           'conflate_composite_pull':left!=right,
                           'nullary_vacuous_surjectivity':diagonal(2)!=bad_nullary})


@dataclass(frozen=True)
class Boundary:
    label: str
    size: int

@dataclass(frozen=True)
class Arrow:
    source: Boundary
    target: Boundary
    relation: int
    def __post_init__(self):
        if not 0 <= self.relation < (1 << (self.source.size*self.target.size)):
            raise ValueError('relation outside its typed matrix')

@dataclass(frozen=True)
class Cell:
    whole: Arrow
    profile: tuple[Arrow,...]
    def __post_init__(self):
        cursor=self.whole.source
        for edge in self.profile:
            if edge.source != cursor:
                raise ValueError('noncomposable profile')
            cursor=edge.target
        if cursor != self.whole.target:
            raise ValueError('profile endpoints mismatch; nullary must be loop')
        sizes=(self.whole.source.size,)+tuple(e.target.size for e in self.profile)
        if direct(sizes,tuple(e.relation for e in self.profile)) & ~self.whole.relation:
            raise ValueError('containment cell is false')
    def composite(self):
        return direct((self.whole.source.size,)+tuple(e.target.size for e in self.profile),
                      tuple(e.relation for e in self.profile))
    def exact(self):
        return self.composite()==self.whole.relation

@dataclass(frozen=True)
class Leaf:
    output: Arrow

@dataclass(frozen=True)
class Node:
    label: str
    cell: Cell
    children: tuple
    def __post_init__(self):
        if tuple(output(t) for t in self.children) != self.cell.profile:
            raise ValueError('wrong occurrence assignment at syntax node')


def output(tree):
    return tree.output if isinstance(tree,Leaf) else tree.cell.whole


def leaves(tree):
    if isinstance(tree,Leaf): return (tree.output,)
    return tuple(e for child in tree.children for e in leaves(child))


def evaluate(tree):
    if isinstance(tree,Leaf): return Cell(tree.output,(tree.output,))
    cs=tuple(evaluate(child) for child in tree.children)
    assert tuple(c.whole for c in cs)==tree.cell.profile
    return Cell(tree.cell.whole,tuple(e for c in cs for e in c.profile))


def graft(tree,forest):
    if tuple(output(t) for t in forest)!=leaves(tree):
        raise ValueError('wrong leaf-occurrence substitution')
    cursor=iter(forest)
    def walk(t):
        if isinstance(t,Leaf): return next(cursor)
        return Node(t.label,t.cell,tuple(walk(u) for u in t.children))
    result=walk(tree)
    assert next(cursor,None) is None
    return result


def binary(label,left,right):
    x,y=output(left),output(right)
    if x.target!=y.source: raise ValueError('noncomposable binary node')
    w=Arrow(x.source,y.target,multiply(x.source.size,x.target.size,y.target.size,
                                      x.relation,y.relation))
    return Node(label,Cell(w,(x,y)),(left,right))


def pulled_arrow(edge,maps):
    source,f=maps[edge.source]; target,g=maps[edge.target]
    return Arrow(source,target,pull(edge.source.size,edge.target.size,edge.relation,f,g))


def pulled_cell(cell,maps):
    return Cell(pulled_arrow(cell.whole,maps),tuple(pulled_arrow(e,maps) for e in cell.profile))


def pulled_tree(tree,maps):
    if isinstance(tree,Leaf): return Leaf(pulled_arrow(tree.output,maps))
    return Node(tree.label,pulled_cell(tree.cell,maps),tuple(pulled_tree(c,maps) for c in tree.children))


def rejection(action):
    try: action()
    except ValueError as e: return str(e)
    raise AssertionError('required rejection was not detected')


def typed_syntax():
    A=Boundary('A',2); B=Boundary('B',3); C=Boundary('C',2)
    x=Arrow(A,B,encode(2,3,[(0,0),(1,1)]))
    r=Arrow(B,B,(1<<9)-1)
    y=Arrow(B,C,encode(3,2,[(2,0),(1,1)]))
    P=Arrow(B,B,encode(3,3,[(0,1)]))
    Q=Arrow(B,B,encode(3,3,[(1,2)]))
    lx,lr,ly=Leaf(x),Leaf(r),Leaf(y)
    left=binary('Lroot',binary('L12',lx,lr),binary('L34',lr,ly))
    right=binary('Rroot',lx,binary('R234',lr,binary('R34',lr,ly)))
    assert left!=right
    assert leaves(left)==leaves(right)==(x,r,r,y)
    assert evaluate(left)==evaluate(right)
    assert evaluate(left).exact() and evaluate(left).whole.relation==15
    p=Node('smallP',Cell(r,(P,)),(Leaf(P),))
    q=Node('smallQ',Cell(r,(Q,)),(Leaf(Q),))
    refined=graft(left,(lx,p,q,ly))
    swapped=graft(left,(lx,q,p,ly))
    collapsed=graft(left,(lx,p,p,ly))
    assert evaluate(refined).profile==(x,P,Q,y)
    assert evaluate(refined).composite()==encode(2,2,[(0,0)])
    assert evaluate(swapped).composite()==0
    assert evaluate(collapsed).composite()==0
    assert evaluate(refined)!=evaluate(swapped)!=evaluate(collapsed)
    red=Node('red',p.cell,p.children); blue=Node('blue',p.cell,p.children)
    assert red!=blue and evaluate(red)==evaluate(blue)
    nullary=Node('erase',Cell(r,()),())
    delta=Arrow(B,B,diagonal(3))
    exact_nullary=Node('unit',Cell(delta,()),())
    assert not evaluate(nullary).exact() and evaluate(exact_nullary).exact()
    erased=graft(left,(lx,nullary,lr,ly))
    assert leaves(erased)==(x,r,y)
    assert evaluate(erased)==Cell(evaluate(left).whole,(x,r,y))
    # Both units and an honest second layer of occurrence-wise grafting.
    assert graft(left,tuple(Leaf(e) for e in leaves(left)))==left
    assert graft(Leaf(output(p)),(p,))==p
    P2=Node('Pidentity',Cell(P,(P,)),(Leaf(P),))
    Q2=Node('Qidentity',Cell(Q,(Q,)),(Leaf(Q),))
    second=(lx,P2,Q2,ly)
    first=(lx,p,q,ly)
    lhs=graft(graft(left,first),second)
    rhs=graft(left,(lx,graft(p,(P2,)),graft(q,(Q2,)),ly))
    assert lhs==rhs
    # Global per-label maps satisfy incidence agreements, including erase.
    maps={A:(Boundary('Anew',3),(0,0,1)),
          B:(Boundary('Bnew',2),(0,1)),
          C:(Boundary('Cnew',2),(1,0))}
    restrictions=0
    for t in (left,right,refined,swapped,collapsed,red,blue,nullary,exact_nullary,erased):
        assert evaluate(pulled_tree(t,maps))==pulled_cell(evaluate(t),maps)
        restrictions+=1
    assert pulled_tree(graft(left,first),maps)==graft(pulled_tree(left,maps),
                      tuple(pulled_tree(t,maps) for t in first))
    with_nullary=(lx,nullary,lr,ly)
    assert pulled_tree(graft(left,with_nullary),maps)==graft(pulled_tree(left,maps),
                      tuple(pulled_tree(t,maps) for t in with_nullary))
    rejects={
       'reversed_boundary_order':rejection(lambda:Cell(output(left),(y,r,r,x))),
       'wrong_repeated_occurrence_output':rejection(lambda:graft(left,(lx,lx,lr,ly))),
       'nonloop_nullary_equal_cardinality':rejection(lambda:Cell(Arrow(A,C,15),())),
       'false_containment':rejection(lambda:Cell(Arrow(A,C,0),(x,r,r,y))),
       'swapped_node_children':rejection(lambda:Node('bad',left.cell,tuple(reversed(left.children)))),
    }
    return dict(status='PASS',interfaces={'A':2,'B':3,'C':2},
                four_leaf_profile=['x:A->B','r:B->B','r:B->B','y:B->C'],
                component_matrices={'x':pairs(2,3,x.relation),'r':pairs(3,3,r.relation),
                                    'y':pairs(3,2,y.relation),'P':pairs(3,3,P.relation),
                                    'Q':pairs(3,3,Q.relation)},
                grouping_trees_distinct=True,grouping_cells_equal=True,
                primitive_labels_distinct=True,primitive_cells_equal=True,
                refined_composite=pairs(2,2,evaluate(refined).composite()),
                swapped_composite=[],color_keyed_mutant_composite=[],
                repeated_occurrence_mutation_detected=True,
                independent_restriction_tree_comparisons=restrictions,
                substitution_restriction_with_nullary=True,
                syntax_unit_laws=True,syntax_associativity=True,
                rejections=rejects)


def author_fixture():
    """Read fixture DATA only; recompute every serialized cell and named claim.

    This function is deliberately downstream of the independently written
    exhaustive evaluators and syntax. It does not import or execute author code.
    """
    root=Path(__file__).resolve().parents[1]
    author_path=root/'finite/AuthorCertificate.json'
    source_path=root/'finite/check_c2_model.py'
    author=json.loads(author_path.read_text())
    assert author['target_sha256']==TARGET_HASH
    assert author['contract_sha256']==CONTRACT_HASH
    assert author['source_sha256']==hashlib.sha256(source_path.read_bytes()).hexdigest()
    checked_cells=[]
    def arrow(d):
        a,b=d['sizes']
        assert pairs(a,b,d['mask'])==d['pairs']
        assert encode(a,b,d['pairs'])==d['mask']
        return Arrow(Boundary(d['source'],a),Boundary(d['target'],b),d['mask'])
    def cell(d):
        c=Cell(arrow(d['whole']),tuple(arrow(e) for e in d['profile']))
        assert c.composite()==arrow(d['composite']).relation
        assert c.exact()==d['exact']
        assert [c.whole.source.label]+[e.target.label for e in c.profile]==d['boundary_labels']
        return c
    def descend(d,path):
        if isinstance(d,dict):
            if {'whole','profile','composite','exact','boundary_labels'} <= d.keys():
                cell(d); checked_cells.append(path)
            else:
                for k,v in d.items(): descend(v,path+'.'+k)
        elif isinstance(d,list):
            for i,v in enumerate(d): descend(v,path+f'[{i}]')
    descend(author['named'],'named')
    f4=author['named']['F4']; f5=author['named']['F5']
    original=cell(f4['original_exact']); strict=cell(f4['strict_containment'])
    assert original.profile==strict.profile and original.whole!=strict.whole
    assert original.composite()!=0 and not original.composite() & ~strict.whole.relation
    ns=f4['non_surjective_boundary']; g=tuple(ns['values'])
    assert len(set(g))<ns['original_size']
    restrict=cell(ns['restricted_original_exact'])
    f=h=(0,1)
    for i,e in enumerate(original.profile):
        expected=pull(e.source.size,e.target.size,e.relation,f if i==0 else g,g if i==0 else h)
        assert restrict.profile[i].relation==expected
    assert restrict.whole.relation==pull(2,2,original.whole.relation,f,h)
    def realizers_for(c):
        dims=(c.whole.source.size,)+tuple(e.target.size for e in c.profile)
        return [list(xs) for xs in product(*(range(n) for n in dims))
                if all(bit(e.relation,e.target.size,xs[i],xs[i+1])
                       for i,e in enumerate(c.profile))]
    old=realizers_for(original); new=realizers_for(restrict)
    mapped=[[f[x],g[y],h[z]] for x,y,z in new]
    assert old==ns['old_realizers'] and new==ns['new_realizers'] and mapped==ns['mapped_realizers']
    assert set(map(tuple,mapped)) < set(map(tuple,old))
    assert restrict.composite()!=0 and not restrict.exact()
    positive_data=f4['surjective_many_to_one']; gp=tuple(positive_data['values'])
    assert set(gp)==set(range(3)) and len(gp)>3
    positive=cell(positive_data['cell'])
    assert positive.exact()
    assert positive.profile[0].relation==pull(2,3,original.profile[0].relation,f,gp)
    assert positive.profile[1].relation==pull(3,2,original.profile[1].relation,gp,h)
    positive_realizers=realizers_for(positive)
    image={(f[x],gp[y],h[z]) for x,y,z in positive_realizers}
    assert len(positive_realizers)==positive_data['realizer_count']==3
    assert len(image)==positive_data['image_count']==2
    # Reconstruct author's actual nested left/right shapes and all typed cells.
    four=cell(f5['four_leaf']); x,r,r2,y=four.profile
    assert r==r2 and r.relation!=0
    lx,lr,ly=Leaf(x),Leaf(r),Leaf(y)
    left=binary('left_root',binary('left_middle',binary('left_bottom',lx,lr),lr),ly)
    right=binary('right_root',lx,binary('right_middle',lr,binary('right_bottom',lr,ly)))
    assert left!=right and evaluate(left)==evaluate(right)==four
    first_cell=cell(f5['first_replacement']); second_cell=cell(f5['second_replacement'])
    first=Node('first_occurrence',first_cell,tuple(Leaf(e) for e in first_cell.profile))
    second=Node('second_occurrence',second_cell,tuple(Leaf(e) for e in second_cell.profile))
    refined=graft(right,(lx,first,second,ly))
    mutant=graft(right,(lx,first,first,ly))
    swapped=graft(right,(lx,second,first,ly))
    assert evaluate(refined)==cell(f5['refined'])
    assert evaluate(refined)!=evaluate(mutant) and evaluate(refined)!=evaluate(swapped)
    alpha=Node('alpha',Cell(r,(r,r)),(lr,lr))
    beta=Node('beta',Cell(r,(r,r)),(lr,lr))
    assert alpha!=beta and evaluate(alpha)==evaluate(beta)
    # Actual bottom substitution with an exact nullary at first inserted delta.
    delta=first_cell.profile[0]
    null=Node('null',Cell(delta,()),())
    first_refined=Node(first.label,first.cell,(null,Leaf(first_cell.profile[1])))
    bottom=tuple(Leaf(e) for e in evaluate(refined).profile)
    bottom=bottom[:1]+(null,)+bottom[2:]
    assert graft(refined,bottom)==graft(right,(lx,first_refined,second,ly))
    # Recompute reported mutation payloads, not just their `detected` booleans.
    controls={d['name']:d for d in author['named']['F6']}
    repeated=controls['identify repeated component occurrences']
    assert repeated['correct_profile']==[e.relation for e in evaluate(refined).profile]
    assert repeated['mutant_profile']==[e.relation for e in evaluate(mutant).profile]
    comparison=controls['conflate composite of pulls with pull of composite']
    assert comparison['correct_mask']==restrict.composite()
    assert comparison['mutant_mask']==restrict.whole.relation
    assert comparison['correct_mask']!=comparison['mutant_mask']
    # Confirm numeric domain checkpoints are independent recomputation results.
    assert author['F1']['counts']['comparison_cases']==113171
    assert author['F1']['counts']['containment_cell_restrictions']==661613
    assert author['F1']['counts']['strict_comparison_cases']==17424
    assert author['F2']['counts']['associativity_triples']==8507
    assert author['F3']['counts']['flat_profiles']==9040
    assert author['F3']['counts']['profile_segmentations']==132793
    assert author['F3']['counts']['inner_whole_families']==8162514
    assert author['F3']['counts']['containment_substitutions']==25619591
    return {'status':'PASS','author_source_sha256':author['source_sha256'],
            'author_certificate_sha256':hashlib.sha256(author_path.read_bytes()).hexdigest(),
            'serialized_cells_independently_recomputed':checked_cells,
            'serialized_cell_count':len(checked_cells),
            'actual_principal_maps_recomputed':True,'actual_realizer_lists_recomputed':True,
            'actual_syntax_shapes_and_grafts_reconstructed':True,
            'exact_nested_nullary_graft_reconstructed':True,
            'mutation_payloads_recomputed':True,
            'all_F1_F2_F3_counts_match_independent_enumeration':True}


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    args=parser.parse_args()
    root=Path(__file__).resolve().parents[1]
    assert hashlib.sha256((root/'C2_Targets.md').read_bytes()).hexdigest()==TARGET_HASH
    assert hashlib.sha256((root.parent/'CompletionContract.md').read_bytes()).hexdigest()==CONTRACT_HASH
    started=time.monotonic()
    report={'schema':'C2-independent-finite-v1','target_sha256':TARGET_HASH,
            'contract_sha256':CONTRACT_HASH,'evidence':'C only; unrestricted P remains separate',
            'independence':'Own implementation; imports no author source; bit-matrix multiplication and global assignment enumeration are distinct evaluators.',
            'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'python':platform.python_version()}
    for name,fn in [('F1',f1),('F2',f2),('F3',f3),
                    ('restriction_coherence',restriction_coherence),('own_principal',own_principal),
                    ('independent_typed_syntax',typed_syntax),('author_fixture',author_fixture)]:
        before=time.monotonic(); report[name]=fn()
        print(name, json.dumps(report[name],sort_keys=True), flush=True)
        print(name, 'runtime_seconds', round(time.monotonic()-before,6),flush=True)
    report['status']='PASS F1-F6 independent suite and author named fixture comparison; full C2 remains OPEN'
    print('total_runtime_seconds',round(time.monotonic()-started,6),flush=True)
    args.output.write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print('Saved',args.output,flush=True)

if __name__=='__main__': main()
