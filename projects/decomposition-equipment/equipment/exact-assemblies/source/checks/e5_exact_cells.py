#!/usr/bin/env python3
"""Independent bounded E5 actual-cell computations; no all-parameter proof."""
import argparse
from collections import Counter
from dataclasses import dataclass, replace
from functools import lru_cache
import importlib.util
from itertools import product, permutations, combinations
import json
from math import prod
from pathlib import Path
import sys

spec=importlib.util.spec_from_file_location('e5_frozen_e4',Path(__file__).parent/'dependencies/e4_completion_cells.py')
w=importlib.util.module_from_spec(spec);sys.modules[spec.name]=w;spec.loader.exec_module(w)
e=w.e;need=e.need;ONE=(0,);COUNT=Counter();EVIDENCE={};MUTATION=None

def span(A,B,rows,word=()):
    rows=tuple(rows);apex=tuple(x for x,a,b in rows)
    return w.WH(tuple(word),e.Span(e.Fn(apex,tuple(A),tuple(a for x,a,b in rows)),e.Fn(apex,tuple(B),tuple(b for x,a,b in rows))))

def finite_map(values,cod): return e.Fn(tuple(range(len(values))),tuple(cod),tuple(values))
def histogram(f): return tuple(sum(v==y for v in f.values) for y in f.cod)
def bijective(f): return len(set(f.values))==len(f.dom)==len(f.cod)
def unit(m): return any(e.times(m,n)==0==e.times(n,m) for n in e.M)
def marks(c): return {'coefficient':bijective(c.coefficient),'normalized':bijective(c.coefficient) and c.scalar==0,'unit':bijective(c.coefficient) and unit(c.scalar)}

def pack_fn(f):
    return {'domain':[repr(x) for x in f.dom],'codomain':[repr(x) for x in f.cod],
            'image_indices':[f.cod.index(y) for y in f.values],'fibre_sizes':list(histogram(f))}

def comparison(path,maps,check=True):
    """Enumerate actual pullback spans and actual comparison coefficient, not its criterion."""
    path=tuple(path);maps=tuple(maps);old=w.composite(path,maps[0].cod).horizontal
    restricted=tuple(w.restrict(h,f,g)[0] for h,f,g in zip(path,maps,maps[1:]))
    target=w.restrict(old,maps[0],maps[-1])[0]
    def old_tuple(z):
        out=(maps[0](z[0]),)
        for i in range(len(path)): out+=(z[2*i+1][1],maps[i+1](z[2*i+2]))
        return out
    c=w.cell(restricted,maps[0].dom,target,e.fid(maps[0].dom),e.fid(maps[-1].dom),w.forest_id(old.word),
             lambda z:(z[0],old_tuple(z),z[-1]))
    f=c.coefficient
    fibres=histogram(f)
    if MUTATION=='deduplicate_internal_lifts':
        # Wrong finite comparison carrier, with same target but one representative per image.
        keep=tuple(next(z for z in f.dom if f(z)==y) for y in dict.fromkeys(f.values))
        f=e.fun(keep,f.cod,f)
    need(f.dom==e.tuples(restricted,maps[0].dom),'comparison retains every actual separately restricted tuple')
    expected=[]
    for a,z,b in f.cod:
        expected.append(prod(sum(x==z[2*i] for x in maps[i].values) for i in range(1,len(path))))
    if check: need(tuple(expected)==histogram(f),'actual whole-run lift fibres equal structural product')
    lhs={(z[0],z[-1]) for z in f.dom};rhs={(a,b) for a,z,b in f.cod}
    if MUTATION=='endpoint_support_is_coefficient':
        observed=tuple(1 for _ in f.cod) if lhs==rhs else histogram(f)
        need(observed==histogram(f),'endpoint support equality is not coefficient equality')
    need(lhs<=rhs,'strict Rel inclusion direction')
    feasible={}
    for a,z,b in f.cod: feasible.setdefault((a,b),[]).append(z)
    support_hit=all(any(all(z[2*i] in maps[i].values for i in range(1,len(path))) for z in zs) for zs in feasible.values())
    need((lhs==rhs)==support_hit,'Rel equality by some lift versus coefficient all unique lifts')
    need(bijective(f)==all(n==1 for n in expected),'computed coefficient bijection criterion')
    COUNT['actual_path_comparisons']+=1;COUNT['target_lift_fibres']+=len(f.cod)
    return c,{'source':len(f.dom),'target':len(f.cod),'fibres':list(fibres),'Rel_equal':lhs==rhs,'coefficient_bijective':bijective(f)}

def relations(A,B):
    pairs=tuple(product(A,B))
    return tuple(span(A,B,((p,*p) for p,bit in zip(pairs,bits) if bit)) for bits in product((0,1),repeat=len(pairs)))

def test_boundary():
    A=(0,1);maps=tuple(finite_map(v,A) for n in range(3) for v in product(A,repeat=n))
    for h,k,f in product(relations(A,A),relations(A,A),maps): comparison((h,k),(e.fid(A),f,e.fid(A)))
    full=(span(ONE,A,(('a',0,0),('b',0,1))),span(A,ONE,(('c',0,0),('d',1,0))))
    examples={}
    for label,values in (('surjective_noninjective',(0,0,1)),('nonsurjective_but_Rel_equal',(0,)),('equal_size_not_iso',(0,0)),('bijection',(1,0)),('empty_source',())):
        c,r=comparison(full,(e.fid(ONE),finite_map(values,A),e.fid(ONE)));examples[label]={**r,'coefficient':pack_fn(c.coefficient)}
    need(examples['surjective_noninjective']['Rel_equal'] and not examples['surjective_noninjective']['coefficient_bijective'],'surjection preserves Rel not coefficient exactness')
    need(examples['equal_size_not_iso']['source']==examples['equal_size_not_iso']['target'] and examples['equal_size_not_iso']['fibres']==[2,0],'equal size does not replace actual bijection')
    missed=(span(ONE,A,(('a',0,1),)),span(A,ONE,(('b',1,0),)))
    _,examples['strict_inclusion']=comparison(missed,(e.fid(ONE),finite_map((0,),A),e.fid(ONE)))
    path=(missed[0],span(A,A,(('middle',1,1),)),missed[1]);fs=(e.fid(ONE),finite_map((0,),A),finite_map((0,),A),e.fid(ONE))
    adjacent=[comparison(path[i:i+2],fs[i:i+3])[1] for i in range(2)];whole=comparison(path,fs)[1]
    need(all(r['coefficient_bijective'] and r['Rel_equal'] for r in adjacent) and not whole['Rel_equal'],'adjacent vacuity fails whole-run transport')
    all_runs=[{'interval':[i,j],**comparison(path[i:j],fs[i:j+1])[1]} for i in range(3) for j in range(i+1,4)]
    if MUTATION=='check_only_adjacent_runs': all_runs=[r for r in all_runs if r['interval'][1]-r['interval'][0]<=2]
    need(any(r['interval']==[0,3] and not r['coefficient_bijective'] for r in all_runs),'retained run registry must include whole composites beyond adjacent pairs')
    examples['adjacent_vacuity']={'adjacent':adjacent,'whole':whole,'all_runs':all_runs}
    nullary=[]
    for n in range(3):
        A=tuple(range(n))
        for m in range(4):
            for values in product(A,repeat=m):
                f=finite_map(values,A);unit_h=w.composite((),A).horizontal;target=w.restrict(unit_h,f,f)[0]
                source=w.composite((),f.dom).horizontal
                c=e.fun(source.span.E,target.span.E,lambda z:(z[0],(f(z[0]),),z[0]))
                expected=len(set(values))==len(values)
                if MUTATION=='nullary_empty_product': expected=True
                need(bijective(c)==expected,'nullary diagonal comparison requires injectivity')
                nullary.append({'old_size':n,'map':list(values),'source':len(c.dom),'target':len(c.cod),'bijective':bijective(c)})
    EVIDENCE['boundary']={'examples':examples,'nullaries':nullary,'exhaustive_bound':'All 16 relations on two points, all ordered pairs, all 7 internal maps with domain size 0..2; exterior maps identity.'}

@dataclass(frozen=True)
class Tree:
    name:str
    children:tuple
    local:object
    leaf:object=None

@lru_cache(None)
def shapes(n):
    if n==1:return (None,)
    return tuple((a,b) for k in range(1,n) for a in shapes(k) for b in shapes(n-k))

def build(shape,leaves,counter):
    if shape is None:
        i=counter[0];counter[0]+=1;return Tree('l'+str(i),(),None,leaves[i])
    children=tuple(build(s,leaves,counter) for s in shape);path=tuple(output(t) for t in children)
    choice=w.composite(path,path[0].span.A,1+counter[0]%2)
    return Tree('n'+str(counter[0])+'_'+''.join(t.name for t in children),children,choice.mu)

def output(t): return t.leaf if t.local is None else t.local.target

def flatten_tree(t):
    if t.local is None:return w.ident(t.leaf)
    return w.subst(t.local,tuple(flatten_tree(c) for c in t.children))

def boundary_range(t):
    if t.local is None:
        i=int(t.name[1:]);return i,i+1
    return boundary_range(t.children[0])[0],boundary_range(t.children[-1])[1]

def transport_local(alpha,fs):
    restricted=tuple(w.restrict(h,f,g)[0] for h,f,g in zip(alpha.path,fs,fs[1:]));target=w.restrict(alpha.target,fs[0],fs[-1])[0]
    def rule(z):
        old=(fs[0](z[0]),)
        for i in range(len(alpha.path)):old+=(z[2*i+1][1],fs[i+1](z[2*i+2]))
        value=alpha.coefficient(old)
        if MUTATION=='rotate_tree_coefficient' and len(alpha.target.span.E)>1:
            candidates=tuple(x for x in alpha.target.span.E if alpha.target.span.left(x)==fs[0](z[0]) and alpha.target.span.right(x)==fs[-1](z[-1]))
            value=candidates[(candidates.index(value)+1)%len(candidates)]
        return z[0],value,z[-1]
    return w.cell(restricted,fs[0].dom,target,e.fid(fs[0].dom),e.fid(fs[-1].dom),alpha.forest,rule,alpha.scalar)

def transport_tree(t,fs):
    if t.local is None:
        i,j=boundary_range(t);return Tree(t.name,(),None,w.restrict(t.leaf,fs[i],fs[j])[0])
    children=tuple(transport_tree(c,fs) for c in t.children)
    cuts=(boundary_range(t)[0],)+tuple(boundary_range(c)[1] for c in t.children)
    local=transport_local(t.local,tuple(fs[i] for i in cuts))
    need(local.path==tuple(output(c) for c in children),'local comparison retains all child interfaces')
    COUNT['retained_tree_local_comparison_squares']+=len(local.coefficient.dom)
    return Tree(t.name,children,local)

def internal_names(t):return (() if t.local is None else (t.name,)+sum((internal_names(c) for c in t.children),()))

def contract(t,name):
    if t.local is None:return t
    children=tuple(contract(c,name) for c in t.children)
    for i,c in enumerate(children):
        if c.name==name:
            row=tuple(c.local if j==i else w.ident(output(d)) for j,d in enumerate(children))
            return Tree(t.name,children[:i]+c.children+children[i+1:],w.subst(t.local,row))
    return Tree(t.name,children,t.local)

def independent_full_transport(t,fs):
    old=flatten_tree(t);restricted=tuple(w.restrict(h,f,g)[0] for h,f,g in zip(old.path,fs,fs[1:]));target=w.restrict(old.target,fs[0],fs[-1])[0]
    table=[]
    for z in e.tuples(restricted,fs[0].dom):
        mapped=tuple(fs[i//2](v) if i%2==0 else v[1] for i,v in enumerate(z))
        table.append((z[0],old.coefficient(mapped),z[-1]))
    return e.Fn(e.tuples(restricted,fs[0].dom),target.span.E,tuple(table))

def test_trees():
    A=(0,1);h=span(A,A,((('edge',a,b),a,b) for a,b in product(A,repeat=2)))
    patterns=((1,0),(0,0,1),(0,),())
    samples=[]
    for n in (2,3,4,5):
        leaves=tuple(h for _ in range(n))
        for shape_index,shape in enumerate(shapes(n)):
            t=build(shape,leaves,[0]);old=flatten_tree(t)
            for values in patterns:
                fs=(e.fid(A),)+tuple(finite_map(values,A) for _ in range(n-1))+(e.fid(A),)
                transported=transport_tree(t,fs);actual=flatten_tree(transported);independent=independent_full_transport(t,fs)
                need(actual.coefficient==independent,'full-tree recursive coefficient equals independent flat coefficient table')
                need(actual.scalar==old.scalar,'all retained tree scalar labels multiply without omission')
                _,flat_report=comparison(old.path,fs)
                need(sorted(histogram(actual.coefficient))==sorted(flat_report['fibres']),'whole-tree target lift fibres agree after opaque old certificate bijection')
                names=internal_names(t)[1:]
                for order in permutations(names):
                    current=t
                    for name in order:
                        current=contract(current,name)
                        got=flatten_tree(transport_tree(current,fs))
                        need(got==actual,'every contraction prefix commutes with actual transport cell')
                        COUNT['contraction_prefix_transport_equalities']+=1
                    need(flatten_tree(current)==old,'all contraction orders preserve whole actual cell')
                COUNT['full_tree_coefficient_maps']+=1
                if n==3 and shape_index==0:
                    samples.append({'shape':repr(shape),'internal_map':list(values),'coefficient':pack_fn(actual.coefficient),'scalar':actual.scalar})
    EVIDENCE['trees']={'binary_shapes_leaves_2_to_5':sum(len(shapes(n)) for n in (2,3,4,5)),
        'internal_maps':[list(v) for v in patterns],'retained_full_coefficient_samples':samples,
        'contractions':'Every permutation of every proper internal-node contraction, and every prefix; recursive and independent flat tables compared.'}


def test_faithful_assembly():
    inverse_cases=0
    for n,m in product(range(4),repeat=2):
        A=tuple(range(n));B=tuple(range(m))
        for f in e.functions(A,B):
            actual=tuple(g for g in e.functions(B,A) if e.fcomp(g,f)==e.fid(A) and e.fcomp(f,g)==e.fid(B))
            need(len(actual)==int(all(x==1 for x in histogram(f))),'actual two-sided reconstruction fibres')
            inverse_cases+=1
    one=span(ONE,ONE,(('x',0,0),));two=span(ONE,ONE,(('a',0,0),('b',0,0)))
    i=w.cell((one,),ONE,two,e.fid(ONE),e.fid(ONE),w.forest_id(()),lambda z:'a')
    p=w.cell((two,),ONE,one,e.fid(ONE),e.fid(ONE),w.forest_id(()),lambda z:'x')
    root=w.subst(p,(i,));stages=(i,p)
    retained=all(marks(c)['normalized'] for c in stages)
    if MUTATION=='root_only_reconstruction':retained=marks(root)['normalized']
    need(marks(root)['normalized'] and not retained,'root identity must not hide retained-stage reconstruction failure')
    flipped=replace(w.ident(two),scalar=1);fliproot=w.subst(flipped,(flipped,))
    need(marks(fliproot)['normalized'] and not marks(flipped)['normalized'] and marks(flipped)['unit'],'normalized root scalar does not recover local identity marks')
    empty=span(ONE,ONE,());emptyid=w.ident(empty)
    need(marks(emptyid)['normalized'],'empty-to-empty actual coefficient is bijective')
    # Nontrivial branching exact assembly; nullary contributes a named scalar and unit tuple.
    a=span(ONE,ONE,(('a0',0,0),('a1',0,0)));b=span(ONE,ONE,(('b0',0,0),('b1',0,0)))
    cp=w.composite((a,b),ONE,1);eta=w.composite((),ONE,1)
    outer=w.composite((cp.horizontal,eta.horizontal),ONE,2).mu
    assembled=w.subst(outer,(cp.mu,eta.mu))
    if MUTATION=='drop_nullary_stage_scalar':assembled=replace(assembled,scalar=e.scalars((outer.scalar,cp.mu.scalar)))
    need(assembled.scalar==e.scalars((outer.scalar,cp.mu.scalar,eta.mu.scalar)),'nullary stage scalar retained in complete assembly')
    need(all(marks(c)['unit'] for c in (cp.mu,eta.mu,outer,assembled)),'actual branching/nullary coefficient exact assembly')
    EVIDENCE['faithful_assembly']={'exhaustive_function_inverse_cases_sizes_0_to_3':inverse_cases,
       'root_mask':{'stages':[pack_fn(c.coefficient) for c in stages],'root':pack_fn(root.coefficient),'root_normalized':marks(root)['normalized'],'retained_normalized':retained},
       'scalar_mask':{'local_scalars':[1,1],'root_scalar':fliproot.scalar},'empty_to_empty':marks(emptyid),'branching_nullary_total_scalar':assembled.scalar}


def test_restrictions():
    A=(0,1);target=span(A,ONE,(('x',0,0),('y',1,0)));f=finite_map((0,0,1),A);g=e.fid(ONE)
    restricted,k=w.restrict(target,f,g);source=span(f.dom,ONE,(('p',0,0),('q',1,0),('r',2,0)))
    factors=0
    for alpha in w.cells((source,),f.dom,target,f,g):
        expected=w.restriction_factor(alpha,f,g,e.fid(f.dom),e.fid(ONE))
        actual=tuple(beta for beta in w.cells((source,),f.dom,restricted,e.fid(f.dom),e.fid(ONE)) if w.subst(k,(beta,))==alpha)
        need(actual==(expected,),'cartesian restriction actual unique factor fibre')
        factors+=1
    # Pullback of a bijective coefficient map stays bijective at fixed endpoints.
    h=span(A,ONE,(('x0',0,0),('x1',0,0),('y0',1,0)))
    renamed=span(A,ONE,(('X0',0,0),('X1',0,0),('Y0',1,0)))
    phi=e.Fn(h.span.E,renamed.span.E,('X1','X0','Y0'))
    hp=w.restrict(h,f,g)[0];rp=w.restrict(renamed,f,g)[0]
    pulled=e.fun(hp.span.E,rp.span.E,lambda z:(z[0],phi(z[1]),z[2]))
    need(bijective(pulled),'cartesian reindexing of actual bijection')
    EVIDENCE['cartesian_vs_internal']={'cartesian_unique_factor_fibres':factors,'restriction_projection_coefficient':pack_fn(k.coefficient),
       'restriction_cell_globular':False,'pulled_bijection':pack_fn(pulled),
       'contrast':'The same finite-span equipment has all these cartesian restrictions, but boundary.strict_inclusion has a nonbijective globular internal comparison.'}


def monoid_congruence(equations):
    blocks=[{m} for m in e.M]
    def merge(a,b):
        aa=next(x for x in blocks if a in x);bb=next(x for x in blocks if b in x)
        if aa is bb:return False
        aa.update(bb);blocks.remove(bb);return True
    for a,b in equations:merge(a,b)
    changed=True
    while changed:
        changed=False
        for block in tuple(tuple(sorted(x)) for x in blocks):
            for a,b,m in product(block,block,e.M):changed=merge(e.times(a,m),e.times(b,m)) or changed
    return tuple(tuple(sorted(b)) for b in sorted(blocks,key=min))

def test_quotients():
    H=monoid_congruence(((0,1),));bad=monoid_congruence(((0,2),))
    units=tuple(unit(m) for m in e.M)
    need(all(len({units[m] for m in b})==1 for b in H),'unit-subgroup quotient preserves unit predicate')
    normalized_invariant=all(len({m==0 for m in b})==1 for b in H)
    if MUTATION=='quotient_invariant_is_existential': normalized_invariant=all(any(m==0 for m in b) or all(m!=0 for m in b) for b in H)
    need(not normalized_invariant,'scalar identity mark not well-defined under nontrivial unit-subgroup quotient')
    need(any(len({units[m] for m in b})>1 for b in bad),'absorbing-zero equation destroys unit mark')
    graph=e.Graph(2,((0,1),));apex=(0,1);double=(0,1,2,3)
    h=e.SH(graph,e.Span(e.fun(apex,ONE,lambda _:0),e.fun(apex,ONE,lambda _:0)))
    doubled=e.SH(graph,e.Span(e.fun(double,ONE,lambda _:0),e.fun(double,ONE,lambda _:0)))
    make=lambda source,target,values:e.scall((source,),ONE,target,e.fid(ONE),e.fid(ONE),((0,1),),lambda z:values[source.span.E.index(z[1])])
    s0=make(h,doubled,(0,1));s1=make(h,doubled,(2,3));d=make(doubled,h,(0,1,0,0))
    left=e.ssub(d,(s0,));right=e.ssub(d,(s1,))
    need(left==e.sid(h) and not bijective(right.coefficient),'doubling-section equation yields actual identity versus constant equation')
    need(left.path==right.path and left.target==right.target and left.blocks==right.blocks,'counterexample is a genuine fixed-profile equation')
    # Actual postcomposition fibres distinguish opcartesian identity from constant.
    def post_fibres(c):
        domain=tuple(e.scells((h,),ONE,h,e.fid(ONE),e.fid(ONE)))
        outputs=tuple(e.ssub(x,(c,)) for x in domain)
        return tuple(sum(x==y for x in outputs) for y in domain)
    idfib=post_fibres(left);constfib=post_fibres(right)
    need(all(x==1 for x in idfib) and any(x!=1 for x in constfib),'actual universal factor test sees quotient-related marked and unmarked cells')
    EVIDENCE['quotients']={'scalar_C2_subgroup_congruence':[list(x) for x in H],'unit_mark_invariant':True,'normalized_mark_invariant':normalized_invariant,
        'identity_equals_absorbing_congruence':[list(x) for x in bad],
        'active_graph':repr(graph),'doubling_sections':{'s0':pack_fn(s0.coefficient),'s1':pack_fn(s1.coefficient),'postmap':pack_fn(d.coefficient)},
        'induced_equation':{'left':pack_fn(left.coefficient),'right':pack_fn(right.coefficient),'left_postcomposition_fibres':list(idfib),'right_postcomposition_fibres':list(constfib)},
        'scope':'Actual equations at an edge-containing active graph. Parameterized full-VE congruence closure and inactive graph preservation are P, not inferred from this finite profile. Fixed-sort full-VE quotient does not fail restriction uniqueness.'}


def test_graph_reconstruction_and_marks():
    path=(e.SH(e.POINT,e.Span(e.fun(('x',),ONE,lambda _:0),e.fun(('x',),ONE,lambda _:0))),)*2
    cells=[]
    for graph in e.all_graphs(2):
        target=e.SH(graph,path[0].span)
        cells.append(e.scall(path,ONE,target,e.fid(ONE),e.fid(ONE),((0,),(1,)),lambda z:'x'))
    need(all(bijective(c.coefficient) and c.scalar==0 for c in cells),'both genuine cross-edge cuts coefficient-exact')
    need(not tuple(e.scells((cells[0].target,),ONE,cells[1].target,e.fid(ONE),e.fid(ONE))),'cross-edge alternate target has no unary factor despite exact coefficient')
    def retained_reconstruction_key(c):
        # A proposed serialization of an exact assembly: removing the whole is
        # an actual information-loss mutation, tested by the same baseline law.
        whole=() if MUTATION=='forget_cross_edges' else (c.target.graph,)
        return (c.path,c.blocks,c.coefficient,c.scalar)+whole
    need(len({retained_reconstruction_key(c) for c in cells})==len(cells),
         'faithful exact-assembly serialization must retain distinct cross-edge wholes')
    census=[]
    for n in range(5):
        for arity in range(1,4):
            for blocks in e.all_blocks(n,arity):
                families={}
                for graph in e.all_graphs(n):
                    signature=tuple(graph.cut(b) for b in blocks);families.setdefault(signature,[]).append(graph)
                cross=tuple((a,b) for a,b in combinations(range(n),2) if not any(a in block and b in block for block in blocks))
                need(all(len(gs)==2**len(cross) for gs in families.values()),'actual graph reconstruction fibre is all cross-edge assignments')
                for signature,gs in families.items():
                    separated=tuple(g for g in gs if not set(g.edges)&set(cross))
                    need(len(separated)==1,'no-cross-edge family uniquely reconstructed')
                    records={(signature,tuple(edge for edge in g.edges if edge in cross)) for g in gs}
                    need(len(records)==len(gs),'retaining cross-edge interaction record repairs reconstruction faithfully')
                    COUNT['graph_reconstruction_fibres']+=1
                census.append({'n':n,'arity':arity,'blocks':blocks,'cross_pairs':len(cross),'fibres':len(families)})
    # Positive opcartesian sample, verified via exhaustive actual factor fibres.
    empty=e.SH(e.EMPTY,path[0].span);positive_path=(path[0],empty)
    domain=e.tuples(positive_path,ONE);whole=e.SH(e.POINT,e.Span(e.fun(domain,ONE,lambda _:0),e.fun(domain,ONE,lambda _:0)))
    mu=e.scall(positive_path,ONE,whole,e.fid(ONE),e.fid(ONE),((0,),()),lambda z:z)
    target=e.SH(e.POINT,e.Span(e.fun(('u','v'),ONE,lambda _:0),e.fun(('u','v'),ONE,lambda _:0)))
    factors=0
    for alpha in e.scells(positive_path,ONE,target,e.fid(ONE),e.fid(ONE)):
        fibre=tuple(beta for beta in e.scells((whole,),ONE,target,e.fid(ONE),e.fid(ONE)) if e.ssub(beta,(mu,))==alpha)
        need(len(fibre)==1,'positive one-nonempty-graph actual universal factor fibre');factors+=1
    zero=replace(mu,scalar=2);x=e.sid(whole);y=replace(x,scalar=1)
    need(x!=y and e.ssub(x,(zero,))==e.ssub(y,(zero,)),'coefficient bijection with nonunit scalar not opcartesian')
    EVIDENCE['graphs_and_marks']={'cross_edge_wholes':[repr(c.target.graph) for c in cells],'same_components':True,'both_normalized_coefficient_exact':True,
       'alternate_whole_factor_count':0,'positive_actual_unique_factor_fibres':factors,
       'nonunit_scalar_actual_factor_collision':True,'partition_census_count':len(census),'max_graph_vertices':4,'max_partition_arity':3,
       'repaired_families':['zero cross-edge graphs, components and actual partition retained','arbitrary cross edges with full labelled interaction edge record retained'],
       'retained_example':{'partition':cells[0].blocks,'graphs':[repr(c.target.graph) for c in cells]},
       'scope':'Single-graph S cells for coefficient versus opcartesian distinction; W actual word cells only for coefficient transport/coherence. W empty word is not identified with its one empty-graph occurrence.'}

MUTATIONS=('deduplicate_internal_lifts','endpoint_support_is_coefficient','check_only_adjacent_runs','nullary_empty_product',
'rotate_tree_coefficient','root_only_reconstruction','drop_nullary_stage_scalar','quotient_invariant_is_existential','forget_cross_edges')

def main():
    global MUTATION
    p=argparse.ArgumentParser();p.add_argument('--mutate',choices=MUTATIONS);p.add_argument('--expect-optimize',type=int,choices=(0,1,2));a=p.parse_args();MUTATION=a.mutate
    try:
        need(a.expect_optimize is None or sys.flags.optimize==a.expect_optimize,'interpreter optimization mode mismatch')
        for test in (test_boundary,test_trees,test_faithful_assembly,test_restrictions,test_quotients,test_graph_reconstruction_and_marks):test()
        result={'status':'PASS','schema':'E5 bounded actual-cell evidence v1','counts':dict(sorted(COUNT.items())),'evidence':EVIDENCE,
          'scalar_encoding':{'0':'monoid identity','1':'nonidentity C2 unit','2':'absorbing nonunit'},
          'limits':['Finite C evidence only; author supplies parameterized P proof. No new Lean claim.',
            'No arbitrary presentation quotient inferred from unary scalar/section samples. Full fixed-sort VE quotient retains cartesian uniqueness.',
            'Tree tests enumerate binary shapes with 2..5 leaves and all internal-contraction orders; arbitrary arity/depth is P. Explicit unary/empty/nullary regressions are separate.',
            'Exact frozen E3/E4 primitives are reused; their full regression suites are not rerun or enlarged here.']};code=0
    except (e.Failure,RuntimeError,ValueError,IndexError,KeyError,TypeError) as error:
        result={'status':'REJECT','mutation':MUTATION,'reason':str(error)};code=1
    print(json.dumps(result,sort_keys=True));return code

if __name__=='__main__':raise SystemExit(main())
