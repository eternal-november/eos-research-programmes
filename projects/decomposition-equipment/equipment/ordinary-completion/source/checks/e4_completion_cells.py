#!/usr/bin/env python3
"""Finite semantic E4 checks, not a term-symbol or all-parameter proof.

Graph-word forests, tuple-span coefficients and global scalar labels are actual
finite data. Frozen E3 supplies only checked graph/groupoid/span primitives.
"""
import argparse
from collections import Counter
from dataclasses import dataclass, replace
from functools import lru_cache
import importlib.util
from itertools import product
import json
from pathlib import Path
import sys

E3_PATH=Path(__file__).resolve().parent/'dependencies/e3_model_cells.py'
spec=importlib.util.spec_from_file_location('e4_frozen_e3',E3_PATH)
e=importlib.util.module_from_spec(spec);sys.modules[spec.name]=e;spec.loader.exec_module(e)
need=e.need
COUNT=Counter()
MUTATION=None

def flat(words): return tuple(g for word in words for g in word)

@dataclass(frozen=True)
class Forest:
    source: tuple
    target: tuple
    cuts: tuple  # one ordered block tuple per target root, including nullary roots

    def __post_init__(self):
        need(len(self.cuts)==len(self.target),'forest retains each output root')
        i=0
        for graph,blocks in zip(self.target,self.cuts):
            run=self.source[i:i+len(blocks)];i+=len(blocks)
            e.validate_blocks(graph,run,blocks)
        need(i==len(self.source),'forest full source allocation')

    def occurrences(self):
        return tuple(j for j,blocks in enumerate(self.cuts) for _ in blocks)

def forest_id(word):
    return Forest(word,word,tuple((tuple(range(g.n)),) for g in word))

def tensor(fs):
    return Forest(flat(f.source for f in fs),flat(f.target for f in fs),flat(f.cuts for f in fs))

def forest_comp(outer,inner):
    need(inner.target==outer.source,'forest composite middle word')
    cuts=[];cursor=0
    for blocks in outer.cuts:
        cuts.append(tuple(tuple(block[v] for v in child) for block,children in
                          zip(blocks,inner.cuts[cursor:cursor+len(blocks)]) for child in children))
        cursor+=len(blocks)
    if MUTATION=='merge_empty_root_occurrences' and len(outer.target)>1 and not any(g.n for g in outer.target):
        cuts=[tuple(() for _ in inner.source)]+[() for _ in outer.target[1:]]
    return Forest(inner.source,outer.target,tuple(cuts))

def weak_compositions(n,k):
    if k==0:
        if n==0: yield ()
    else:
        for a in range(n+1):
            for rest in weak_compositions(n-a,k-1): yield (a,)+rest

@lru_cache(None)
def forests(source,target):
    answer=[]
    for sizes in weak_compositions(len(source),len(target)):
        runs=[];cursor=0
        for graph,n in zip(target,sizes):
            run=source[cursor:cursor+n];cursor+=n
            runs.append(tuple(bs for bs in e.all_blocks(graph.n,n)
                              if all(graph.cut(b)==g for b,g in zip(bs,run))))
        answer.extend(Forest(source,target,cuts) for cuts in product(*runs))
    return tuple(answer)

@dataclass(frozen=True)
class WH:
    word: tuple
    span: e.Span

@dataclass(frozen=True)
class WC:
    path: tuple
    start: tuple
    target: WH
    left: e.Fn
    right: e.Fn
    forest: Forest
    coefficient: e.Fn
    scalar: int

    def __post_init__(self):
        end=self.path[-1].span.B if self.path else self.start
        need((self.left.dom,self.right.dom)==(self.start,end),'word cell boundary domains')
        need((self.left.cod,self.right.cod)==(self.target.span.A,self.target.span.B),'word cell boundary codomains')
        need(self.forest.source==flat(h.word for h in self.path) and self.forest.target==self.target.word,
             'word cell entire graph-word profile')
        need(self.coefficient.dom==e.tuples(self.path,self.start) and self.coefficient.cod==self.target.span.E,
             'word coefficient full tuple type')
        need(all(self.target.span.left(self.coefficient(z))==self.left(z[0]) and
                 self.target.span.right(self.coefficient(z))==self.right(z[-1]) for z in self.coefficient.dom),
             'word coefficient endpoint equations')
        need(self.scalar in e.M,'word global scalar')

def cell(path,start,target,left,right,forest,rule,scalar=0):
    p=tuple(path)
    return WC(p,start,target,left,right,forest,e.fun(e.tuples(p,start),target.span.E,rule),scalar)

def ident(h):
    return cell((h,),h.span.A,h,e.fid(h.span.A),e.fid(h.span.B),forest_id(h.word),lambda z:z[1])

def subst(alpha,row,empty_map=None):
    need(len(row)==len(alpha.path),'word substitution full arity')
    if not row:
        need(empty_map is not None and empty_map.cod==alpha.start,'word nullary map retained')
        return cell((),empty_map.dom,alpha.target,e.fcomp(alpha.left,empty_map),e.fcomp(alpha.right,empty_map),
                    alpha.forest,lambda z:alpha.coefficient((empty_map(z[0]),)),alpha.scalar)
    need(all(c.target==h for c,h in zip(row,alpha.path)),'word substitution full profiles')
    need(all(c.right==d.left for c,d in zip(row,row[1:])),'word substitution shared boundary maps')
    path=flat(c.path for c in row)
    def rule(z):
        out=(row[0].left(z[0]),);cursor=0
        for c in row:
            run=z[2*cursor:2*(cursor+len(c.path))+1]
            out+=(c.coefficient(run),c.right(run[-1]));cursor+=len(c.path)
        return alpha.coefficient(out)
    m=e.scalars([alpha.scalar]+[c.scalar for c in row if not (MUTATION=='drop_nullary_scalar' and not c.path)])
    return cell(path,row[0].start,alpha.target,e.fcomp(alpha.left,row[0].left),e.fcomp(alpha.right,row[-1].right),
                forest_comp(alpha.forest,tensor(tuple(c.forest for c in row))),rule,m)

def cells(path,start,target,left,right):
    domain=e.tuples(path,start)
    fibres=tuple(tuple(x for x in target.span.E if target.span.left(x)==left(z[0]) and
                       target.span.right(x)==right(z[-1])) for z in domain)
    for f in forests(flat(h.word for h in path),target.word):
        for values in product(*fibres):
            for m in e.M: yield WC(path,start,target,left,right,f,e.Fn(domain,target.span.E,values),m)

@dataclass(frozen=True)
class Choice:
    horizontal: WH
    mu: WC
    untag: e.Fn
    weight: int


def composite(path,start,choice=0):
    """An actual span with an actual universal map, not only a Comp label."""
    path=tuple(path);domain=e.tuples(path,start);end=path[-1].span.B if path else start
    apex=domain if choice==0 else tuple((choice,z) for z in reversed(domain))
    untag=e.fun(apex,domain,lambda x:x if choice==0 else x[1])
    tag=lambda z:z if choice==0 else (choice,z)
    span=e.Span(e.fun(apex,start,lambda x:untag(x)[0]),e.fun(apex,end,lambda x:untag(x)[-1]))
    word=flat(h.word for h in path)
    if MUTATION=='erase_empty_word_occurrence': word=tuple(g for g in word if g.n)
    h=WH(word,span);weight=0 if choice==0 else 1
    mu=cell(path,start,h,e.fid(start),e.fid(end),forest_id(word),lambda z:tag(z),weight)
    return Choice(h,mu,untag,weight)

def factor(alpha,j,n,choice=0):
    start=alpha.start if j==0 else alpha.path[j-1].span.B
    comp=composite(alpha.path[j:j+n],start,choice)
    p=alpha.path[:j]+(comp.horizontal,)+alpha.path[j+n:]
    def expand(z):
        x=comp.untag(z[2*j+1])
        if MUTATION=='reverse_context_coefficient' and len(x)>3:
            # Wrong but still endpoint-compatible bijection: an actual semantic mutation.
            fibre=tuple(t for t in comp.untag.cod if t[0]==x[0] and t[-1]==x[-1])
            x=fibre[(fibre.index(x)+1)%len(fibre)]
        return z[:2*j]+x+z[2*j+3:]
    m=e.times(alpha.scalar,comp.weight)  # chosen weights 0,1 are self-inverse units
    if MUTATION=='forget_factor_scalar': m=0
    return cell(p,alpha.start,alpha.target,alpha.left,alpha.right,alpha.forest,
                lambda z:alpha.coefficient(expand(z)),m)

def insert_mu(beta,j,mu):
    row=[ident(h) for h in beta.path];row[j]=mu
    return subst(beta,tuple(row))

def restrict(h,f,g):
    apex=tuple((a,x,b) for a in f.dom for x in h.span.E for b in g.dom
               if f(a)==h.span.left(x) and g(b)==h.span.right(x))
    r=WH(h.word,e.Span(e.fun(apex,f.dom,lambda z:z[0]),e.fun(apex,g.dom,lambda z:z[2])))
    k=cell((r,),f.dom,h,f,g,forest_id(h.word),lambda z:z[1][1])
    return r,k

def restriction_factor(alpha,f,g,u,v):
    r,_=restrict(alpha.target,f,g)
    return cell(alpha.path,alpha.start,r,u,v,alpha.forest,
                lambda z:(u(z[0]),alpha.coefficient(z),v(z[-1])),alpha.scalar)

def embed_h(h):
    s=e.embed_h(h)
    word=(s.graph,) if MUTATION!='forget_old_whole' else (e.Graph(s.graph.n),)
    return WH(word,s.span)

def embed(c):
    path=tuple(embed_h(h) for h in c.path);target=embed_h(c.target)
    blocks=tuple(sorted(c.blocks)) if MUTATION=='sort_old_partition' else c.blocks
    m=0 if MUTATION=='forget_old_scalar' else c.scalar
    return cell(path,e.regular(c.start),target,e.fmap(c.left),e.fmap(c.right),
                Forest(flat(h.word for h in path),target.word,(blocks,)),lambda z:e.fmap(c.left)(z[0]),m)

def refinement(row):
    images=tuple(embed(c) for c in row)
    return frozenset(images) if MUTATION=='forget_refinement_occurrence' else images

ONE=(0,)
def simple(word,apex=('x',),A=ONE,B=ONE):
    return WH(tuple(word),e.Span(e.fun(apex,A,lambda _:A[0]),e.fun(apex,B,lambda _:B[0])))

def test_nonrepresentable_and_new():
    p=e.GH(e.POINT,e.aid(0));path=(p,p)
    cells_old=tuple(e.gdirect(g,((0,),(1,)),(e.aid(0),e.aid(0))) for g in e.all_graphs(2))
    need(cells_old[0].path==path==cells_old[1].path,'actual same old nonreconstructive path')
    # Exhaustive graph-coordinate candidates at r=2; unary cut condition is independent
    # of all additional term constructors, spans, grades and scalars (uniform P proof).
    for graph in e.all_graphs(2):
        maps=[forests((graph,),(c.target.graph,)) for c in cells_old]
        need(not all(maps),'no one graph grade maps to both retained wholes')
        COUNT['nonrepresentable_graph_coordinate_candidates']+=1
    images=tuple(embed(c) for c in cells_old)
    comp=composite(images[0].path,images[0].start)
    need(len(comp.horizontal.word)==2 and all(len(embed_h(c.target).word)==1 for c in cells_old),
         'genuine completed two-occurrence horizontal')
    for alpha in images:
        beta=factor(alpha,0,2)
        need(insert_mu(beta,0,comp.mu)==alpha,'each distinct whole genuinely factors through completion')
        COUNT['nonreconstructive_completed_whole_factors']+=1
    # No forest inverse exists between this word and either old one-graph whole.
    for alpha in images:
        need(not forests(alpha.target.word,comp.horizontal.word),'new composite not old whole up to graph-word isomorphism')
        COUNT['new_not_old_graph_word_isomorphism_obstructions']+=1
    # Universal nullary [] is not identified with old [empty graph].
    old_empty=simple((e.EMPTY,));unit=composite((),ONE)
    need(unit.horizontal.word==() and old_empty.word==(e.EMPTY,),'empty word differs from empty graph occurrence')
    need(forests((),(e.EMPTY,)) and not forests((e.EMPTY,),()),'old empty graph is not new unit')
    assembly=Forest((e.POINT,e.EMPTY),(e.POINT,),(((0,),()),))
    section=Forest((e.POINT,),(e.POINT,e.EMPTY),(((0,),),()))
    need(forest_comp(assembly,section)==forest_id((e.POINT,)),'empty occurrence assembly has right inverse')
    need(forest_comp(section,assembly)!=forest_id((e.POINT,e.EMPTY)),'empty occurrence assembly is not invertible')
    COUNT['unnormalized_occurrence_obstructions']+=3

def test_contextual_bijections():
    a=simple((e.POINT,),('x','y'));b=simple((e.POINT,),('z',));empty=simple((e.EMPTY,),('v',))
    context=simple((e.EMPTY,),('u','v'))
    target=simple((e.Graph(2,((0,1),)),),('q','r'))
    paths=((a,b),(context,a,b),(a,b,empty),(context,a,b,empty))
    for p in paths:
        j=p.index(a)
        for choice in (0,1,2):
            cp=composite(p[j:j+2],ONE,choice);compressed=p[:j]+(cp.horizontal,)+p[j+2:]
            expanded=tuple(cells(p,ONE,target,e.fid(ONE),e.fid(ONE)))
            reduced=tuple(cells(compressed,ONE,target,e.fid(ONE),e.fid(ONE)))
            forward={beta:insert_mu(beta,j,cp.mu) for beta in reduced}
            need(len(set(forward.values()))==len(reduced),'context precomposition is injective on actual cells')
            need(set(forward.values())==set(expanded),'context precomposition is surjective on actual cells')
            for alpha in expanded:
                beta=factor(alpha,j,2,choice)
                need(forward[beta]==alpha and factor(forward[beta],j,2,choice)==beta,'actual contextual factor inverse equations')
                COUNT['actual_contextual_composite_cell_bijections']+=1
            COUNT['complete_contextual_fibre_pairs']+=1
    # Zero-arity and singletons, including two-sided nonempty surrounding words.
    for p in ((a,), (empty,a,empty)):
        t=simple((e.POINT,),('q','r'))
        for j in range(len(p)+1):
            for choice in (0,1):
                cp=composite((),ONE,choice)
                expanded=tuple(cells(p,ONE,t,e.fid(ONE),e.fid(ONE)))
                reduced=tuple(cells(p[:j]+(cp.horizontal,)+p[j:],ONE,t,e.fid(ONE),e.fid(ONE)))
                need({insert_mu(beta,j,cp.mu) for beta in reduced}==set(expanded),'nullary full contextual fibre')
                for alpha in expanded:
                    beta=factor(alpha,j,0,choice)
                    need(insert_mu(beta,j,cp.mu)==alpha,'nullary contextual inverse scalar and coefficient')
                    COUNT['actual_nullary_contextual_cell_bijections']+=1
        for alpha in cells(p,ONE,t,e.fid(ONE),e.fid(ONE)):
            cp=composite(p[:1],ONE);beta=factor(alpha,0,1)
            need(insert_mu(beta,0,cp.mu)==alpha,'singleton genuine composite')
            COUNT['actual_singleton_composite_cells']+=1
    # Noninvertible scalar is not an alternative universal choice.
    cp=composite((a,b),ONE);bad=replace(cp.mu,scalar=2)
    left=ident(cp.horizontal);right=replace(left,scalar=1)
    need(left!=right and subst(left,(bad,))==subst(right,(bad,)), 'absorbing-scalar assembly has nonunique factors')
    COUNT['nonuniversal_scalar_collision']+=1

def test_nonidentity_boundaries():
    A=(0,1);B=('middle',);C=('c0','c1')
    P=('p0','p1');Q=('q0','q1')
    a=WH((e.POINT,),e.Span(e.Fn(P,A,A),e.fun(P,B,lambda _:B[0])))
    b=WH((e.POINT,),e.Span(e.fun(Q,B,lambda _:B[0]),e.Fn(Q,C,C)))
    prefix=WH((e.EMPTY,),e.Span(e.fid(A),e.fid(A)))
    suffix=WH((e.EMPTY,),e.Span(e.fid(C),e.fid(C)))
    target=simple((e.Graph(2,((0,1),)),),('x','y'))
    left=e.fun(A,ONE,lambda _:0);right=e.fun(C,ONE,lambda _:0)
    path=(prefix,a,b,suffix)
    for choice in (0,1):
        cp=composite((a,b),A,choice);short=(prefix,cp.horizontal,suffix)
        source=tuple(cells(path,A,target,left,right))
        factors=tuple(cells(short,A,target,left,right))
        pre={beta:insert_mu(beta,1,cp.mu) for beta in factors}
        need(set(pre.values())==set(source) and len(set(pre.values()))==len(factors),
             'complete composite bijection with genuinely noninjective outside boundaries')
        for alpha in source:
            beta=factor(alpha,1,2,choice)
            need(pre[beta]==alpha,'context factor preserves nonidentity full boundary profile')
            COUNT['nonidentity_boundary_contextual_cell_bijections']+=1

def test_forest_category():
    graphs=(e.EMPTY,e.POINT,e.Graph(2),e.Graph(2,((0,1),)))
    words=((),)+tuple((g,) for g in graphs)+tuple((g,h) for g,h in product(graphs,repeat=2) if g.n+h.n<=2)
    outgoing={w:tuple(f for v in words for f in forests(w,v)) for w in words}
    for a in words:
        for f in outgoing[a]:
            need(forest_comp(f,forest_id(a))==f and forest_comp(forest_id(f.target),f)==f,
                 'actual nonidentity forest category unit laws')
            for g in outgoing[f.target]:
                fg=forest_comp(g,f)
                need(fg.occurrences()==tuple(g.occurrences()[j] for j in f.occurrences()),
                     'forest substitution preserves actual root occurrence allocation')
                for h in outgoing[g.target]:
                    need(forest_comp(h,fg)==forest_comp(forest_comp(h,g),f),
                         'actual nonidentity forest associativity')
                    COUNT['nonidentity_forest_associativity_diagrams']+=1
            COUNT['nonidentity_forest_unit_pairs']+=1
    sample=Forest((e.POINT,e.POINT),(e.Graph(2,((0,1),)),),(((1,),(0,)),))
    void=Forest((),(e.EMPTY,),((),))
    fs=(sample,void,forest_id((e.EMPTY,)))
    for f,g in product(fs,repeat=2):
        need(forest_comp(tensor((f,g)),tensor((forest_id(f.source),forest_id(g.source))))==tensor((f,g)),
             'forest tensor identity interchange')
        COUNT['forest_tensor_interchange_diagrams']+=1

def test_restrictions():
    h=simple((e.POINT,e.EMPTY),('q','r'));f=e.fun((0,1),ONE,lambda _:0)
    r,k=restrict(h,f,f)
    need(len(r.span.E)==8,'word restriction retains full endpoint lift fibre')
    for alpha in cells((h,),ONE,h,e.fid(ONE),e.fid(ONE)):
        u=e.fun(ONE,(0,1),lambda _:0);v=e.fun(ONE,(0,1),lambda _:1)
        beta=restriction_factor(alpha,f,f,u,v)
        need(subst(k,(beta,))==alpha,'actual word restriction beta')
        need(restriction_factor(subst(k,(beta,)),f,f,u,v)==beta,'actual word restriction eta')
        COUNT['word_restriction_factor_cells']+=1

# Trees store actual chosen composites and their flattened universal cells.
@dataclass(frozen=True)
class Tree:
    h: WH
    leaves: tuple
    universal: WC

def leaf(h): return Tree(h,(h,),ident(h))
def node(children,choice=0):
    children=tuple(children)
    cp=composite(tuple(t.h for t in children),ONE,choice)
    u=subst(cp.mu,tuple(t.universal for t in children),e.fid(ONE)) if children else cp.mu
    return Tree(cp.horizontal,flat(t.leaves for t in children),u)

def compare(a,b):
    need(a.leaves==b.leaves,'coherence same flattened leaf path')
    inverse={a.universal.coefficient(z):z for z in a.universal.coefficient.dom}
    need(len(inverse)==len(a.h.span.E),'tree actual universal coefficient bijection')
    m=e.times(a.universal.scalar,b.universal.scalar)
    if MUTATION=='omit_choice_scalar_comparison': m=0
    return cell((a.h,),ONE,b.h,e.fid(ONE),e.fid(ONE),forest_id(a.h.word),
                lambda z:b.universal.coefficient(inverse[z[1]]),m)

def then(f,g): return subst(g,(f,))
def lift(children,target_children,maps,choice=0):
    """Tensor actual unary cells, then factor their common universal source."""
    a=node(children,choice);b=node(target_children,choice)
    cp_a=composite(tuple(t.h for t in children),ONE,choice)
    cp_b=composite(tuple(t.h for t in target_children),ONE,choice)
    multi=subst(cp_b.mu,tuple(maps))
    unary=factor(multi,0,len(children),choice)
    need(unary.path==(a.h,) and unary.target==b.h,'lift actual chosen horizontal composites')
    return unary

def test_coherence():
    hs=[simple((g,),apex) for g,apex in ((e.POINT,('a','b')),(e.EMPTY,('c',)),(e.POINT,('d','e')),(e.POINT,('f',)))]
    a,b,c,d=map(leaf,hs)
    for choice in (0,1,2):
        N=lambda *ts:node(ts,choice)
        ab,bc,cd=N(a,b),N(b,c),N(c,d)
        t0=N(N(ab,c),d);t1=N(ab,cd);t2=N(a,N(b,cd));t3=N(a,N(bc,d));t4=N(N(a,bc),d)
        # The long pentagon side uses tensor-whiskered local associators.
        long1=lift((N(ab,c),d),(N(a,bc),d),(compare(N(ab,c),N(a,bc)),ident(d.h)),choice)
        long2=compare(t4,t3)
        long3=lift((a,N(bc,d)),(a,N(b,cd)),(ident(a.h),compare(N(bc,d),N(b,cd))),choice)
        short=then(compare(t0,t1),compare(t1,t2))
        long=then(then(long1,long2),long3)
        need(short==long==compare(t0,t2),'actual associator pentagon, including whiskering')
        need(subst(short,(t0.universal,))==t2.universal,'pentagon actual flattened universal factor')
        COUNT['actual_pentagon_diagrams']+=1
        I=N();left=N(N(a,I),b);right=N(a,N(I,b));ab=N(a,b)
        left_unitor=compare(N(I,b),b);right_unitor=compare(N(a,I),a)
        route1=then(compare(left,right),lift((a,N(I,b)),(a,b),(ident(a.h),left_unitor),choice))
        route2=lift((N(a,I),b),(a,b),(right_unitor,ident(b.h)),choice)
        need(route1==route2==compare(left,ab),'actual unitors triangle')
        COUNT['actual_triangle_diagrams']+=1
        for tree in (t0,t1,t2,t3,t4,left,right,ab):
            direct=node(tuple(leaf(h) for h in tree.leaves),choice)
            f=compare(tree,direct);g=compare(direct,tree)
            need(then(f,g)==ident(tree.h) and then(g,f)==ident(direct.h),'actual reassociation comparison inverse')
            COUNT['actual_coherence_inverse_pairs']+=1
    choices=[node((a,b,c),i) for i in (0,1,2)]
    for i,j,k in product(range(3),repeat=3):
        need(then(compare(choices[i],choices[j]),compare(choices[j],choices[k]))==compare(choices[i],choices[k]),
             'three-choice actual comparison cocycle')
        need(subst(compare(choices[i],choices[j]),(choices[i].universal,))==choices[j].universal,
             'choice comparison takes actual universal cell to actual universal cell')
        COUNT['actual_alternate_choice_cocycles']+=1

def test_old_profiles_refinements_bad_quotients():
    grades=(e.Arrow(0,1,(1,2,0)),e.aid(1),e.Arrow(1,2,(1,0,2)))
    # Full old graph/scalar fibres at small graph sizes and arities; span map uniquely forced.
    for n in range(4):
        for g in e.all_graphs(n):
            for arity in range(1,4):
                gs=grades[:arity]
                for bs in e.all_blocks(n,arity):
                    c=e.gdirect(g,bs,gs,0);images=tuple(embed(replace(c,scalar=m)) for m in e.M)
                    actual=tuple(cells(images[0].path,images[0].start,images[0].target,images[0].left,images[0].right))
                    old=tuple(embed(x) for x in e.gcells(c.path,c.start,c.target,c.left,c.right))
                    need(set(actual)==set(old) and len(actual)==len(old),'full original-profile fibre bijection')
                    need(len(set(images))==len(e.M),'every original scalar witness retained')
                    for image in images: need(subst(ident(image.target),(image,))==image,'old-cell image identity')
                    COUNT['old_full_profile_fibre_checks']+=1
    for m in e.M:
        c=e.GC((),0,e.GH(e.EMPTY,e.aid(0)),e.aid(0),e.aid(0),(),m)
        z=embed(c);need(z.scalar==m and z.forest.cuts==((),),'old nullary full profile and scalar retained')
        COUNT['old_nullary_scalar_profiles']+=1
    # Principal N=6 C5 fixture, three interfaces, nontrivial grades, repeated middle types.
    blocks=((0,),(1,3),(2,4),(5,));gs=(e.Arrow(0,1,(1,2,0)),e.aid(1),e.aid(1),e.Arrow(1,2,(1,0,2)))
    edges=((0,1),(1,2),(1,3),(2,4),(3,4),(4,5))
    wholes=(e.Graph(6,edges),e.Graph(6,tuple(sorted(edges+((0,5),)))))
    a,b=(e.gdirect(g,blocks,gs,1) for g in wholes)
    need(a.path==b.path and a.path[1]==a.path[2] and embed(a).target!=embed(b).target,'whole and repeated occurrence profiles retained')
    split=e.gdirect(e.Graph(2,((0,1),)),((0,),(1,)),(e.aid(1),e.aid(1)),1)
    row=[e.gid(h) for h in a.path];row[1]=split
    row2=[e.gid(h) for h in a.path];row2[2]=split
    refined=e.gsub(a,tuple(row));refined2=e.gsub(a,tuple(row2))
    need(embed(refined)==subst(embed(a),tuple(embed(x) for x in row)),'old C5 substitution preserved with local scalar')
    need(refinement(tuple(row))!=refinement(tuple(row2)),'distinct occurrence-indexed refinements retained')
    x=replace(e.gid(a.path[1]),scalar=0);y=replace(x,scalar=1)
    need(refinement((x,y))!=refinement((y,x)),'same total scalar does not erase local refinement witnesses')
    for m in e.M:
        pairs=tuple((s,t) for s,t in product(e.M,repeat=2) if e.times(s,t)==m)
        images=tuple((embed(replace(x,scalar=s)),embed(replace(x,scalar=t))) for s,t in pairs)
        need(len(images)==len(set(images)),'original scalar factorization pairs remain distinct')
        COUNT['old_scalar_factorization_pairs']+=len(pairs)
    # The author's principal six-leaf opposite refinement keeps both repeated cuts.
    opposite=e.gdirect(e.Graph(2,((0,1),)),((1,),(0,)),(e.aid(1),e.aid(1)),0)
    row_both=(e.gid(a.path[0]),split,opposite,e.gid(a.path[3]))
    six=e.gsub(a,row_both)
    need(six.blocks==((0,),(1,),(3,),(4,),(2,),(5,)), 'principal opposite repeated-slot cut coordinates')
    need(embed(six)==subst(embed(a),tuple(embed(x) for x in row_both)), 'principal opposite C5 refinement preservation')
    # Actual proper interval factorization, retaining the intermediate whole and both scalars.
    U=(1,2,3,4);mid=a.target.graph.cut(U)
    for m in e.M:
        pairs=tuple((s,t) for s,t in product(e.M,repeat=2) if e.times(s,t)==m);images=[]
        for s,t in pairs:
            inner=e.gdirect(mid,((0,2),(1,3)),(e.aid(1),e.aid(1)),t)
            outer=e.gdirect(a.target.graph,((0,),U,(5,)),(gs[0],e.aid(1),gs[3]),s)
            factors=(e.gid(a.path[0]),inner,e.gid(a.path[3]))
            need(e.gsub(outer,factors)==replace(a,scalar=m),'actual original proper-interval scalar factorization')
            need(subst(embed(outer),tuple(embed(c) for c in factors))==embed(replace(a,scalar=m)),
                 'proper-interval scalar factorization preserved by ordinary comparison')
            images.append((embed(outer),embed(inner)))
            COUNT['actual_old_proper_interval_scalar_factor_pairs']+=1
        need(len(set(images))==len(pairs),'proper-interval factor pairs are not collapsed')
    zero=replace(x,scalar=2)
    need(x!=y and e.gsub(x,(zero,))==e.gsub(y,(zero,)), 'original absorbing scalar destroys factor uniqueness')
    need(embed(x)!=embed(y) and subst(embed(x),(embed(zero),))==subst(embed(y),(embed(zero),)),
         'declaring original absorbing scalar universal would force a forbidden old equality')
    COUNT['original_marked_universality_cancellation_obstructions']+=1
    # Bad proposed completions are explicit noninjective quotient maps, not fake flags.
    w0,w1=embed(a),embed(b)
    forget_whole=lambda c:(c.path,c.target.span,c.left,c.right,c.forest.cuts,c.coefficient,c.scalar)
    need(w0!=w1 and forget_whole(w0)==forget_whole(w1),'bad graph-forgetting completion identifies distinct wholes')
    swapped=e.gdirect(e.Graph(2),((1,),(0,)),(e.aid(0),e.aid(0)),0)
    straight=e.gdirect(e.Graph(2),((0,),(1,)),(e.aid(0),e.aid(0)),0)
    w0,w1=embed(swapped),embed(straight)
    forget_cut=lambda c:(c.path,c.target,c.left,c.right,c.coefficient,c.scalar)
    need(w0!=w1 and forget_cut(w0)==forget_cut(w1),'bad witness quotient identifies distinct parallel cuts')
    z0,z1=embed(x),embed(y)
    need(z0!=z1 and replace(z1,scalar=0)==z0,'bad scalar quotient identifies distinct parallel witnesses')
    COUNT['explicit_bad_completion_collisions']+=3
    COUNT['principal_C5_nonreconstructive_refinement_fixture']+=1

def test_baseline_rel_span():
    # Graph-free tuple Span composites only: regression, never positive E4 class.
    a=simple((),('a','b'));b=simple((),('c','d'));target=simple((),('x','y'))
    for alpha in cells((a,b),ONE,target,e.fid(ONE),e.fid(ONE)):
        beta=factor(alpha,0,2);cp=composite((a,b),ONE)
        need(insert_mu(beta,0,cp.mu)==alpha,'representable Span baseline actual factors')
        COUNT['span_baseline_cell_factors']+=1
    A=(0,1);B=(0,1);C=(0,1)
    relations=tuple(frozenset(z for z,b in zip(product(A,B),bits) if b) for bits in product((0,1),repeat=4))
    comp=lambda r,s:frozenset((a,c) for a in A for c in C if any((a,b) in r and (b,c) in s for b in B))
    identity=frozenset((a,a) for a in A)
    for r,s,t in product(relations,repeat=3):
        need(comp(comp(r,s),t)==comp(r,comp(s,t)),'Rel baseline associativity')
        COUNT['rel_baseline_associativity']+=1
    for r in relations: need(comp(identity,r)==r==comp(r,identity),'Rel baseline units')

MUTATIONS=('erase_empty_word_occurrence','reverse_context_coefficient','forget_factor_scalar',
           'omit_choice_scalar_comparison','forget_old_whole','sort_old_partition','forget_old_scalar',
           'forget_refinement_occurrence','drop_nullary_scalar','merge_empty_root_occurrences')

def main():
    global MUTATION
    parser=argparse.ArgumentParser();parser.add_argument('--mutate',choices=MUTATIONS)
    parser.add_argument('--expect-optimize',type=int,choices=(0,1,2));args=parser.parse_args();MUTATION=args.mutate
    try:
        need(args.expect_optimize is None or sys.flags.optimize==args.expect_optimize,'interpreter optimization mode mismatch')
        for test in (test_nonrepresentable_and_new,test_contextual_bijections,test_nonidentity_boundaries,test_forest_category,test_restrictions,test_coherence,
                     test_old_profiles_refinements_bad_quotients,test_baseline_rel_span): test()
        result={'status':'PASS','schema':'E4 bounded actual-cell evidence v1','counts':dict(sorted(COUNT.items())),
                'fixture':{'principal_N':6,'interfaces':3,'groupoid_automorphisms':6,'scalar_monoid':'C2 plus absorbing zero',
                           'universal_choices':3},
                'limits':['Finite semantic evidence, not the uniform presentation/completion universal-property proof.',
                          'Graph-word model separates the free unmarked C5 envelopes; it is not asserted to be their free completion.',
                          'Nonrepresentability for all V horizontal terms uses the separately proved graph-grading invariant.',
                          'Rel/Span evidence is regression only; no new full Lean mechanization.']};code=0
    except (e.Failure,ValueError,IndexError,KeyError) as error:
        result={'status':'REJECT','mutation':MUTATION,'reason':str(error)};code=1
    print(json.dumps(result,sort_keys=True));return code

if __name__=='__main__': raise SystemExit(main())
