#!/usr/bin/env python3
"""Bounded E3 actual-cell checks; no proof oracle and no optimization-sensitive assert.

Direct graph/groupoid cells and full graph/Span cells are implemented separately.
The latter uses the tuple coordinates also used in the independently completed E2
regression, but is not imported from that package. All profiles remain explicit.
"""
from dataclasses import dataclass, replace
from itertools import product, permutations, combinations
from functools import lru_cache
from collections import Counter
import argparse
import json
import sys

class Failure(RuntimeError):
    pass

def need(b, why):
    if not b:
        raise Failure(why)

COUNT = Counter()
MUTATION = None
M = (0, 1, 2)  # identity, involution, absorbing zero

def times(a, b):
    return 2 if a == 2 or b == 2 else (a + b) % 2

def scalars(xs):
    x = 0
    for y in xs:
        x = times(x, y)
    return x

@dataclass(frozen=True)
class Graph:
    n: int
    edges: tuple = ()

    def __post_init__(self):
        need(self.n >= 0 and tuple(sorted(set(self.edges))) == self.edges,
             'ordered graph canonical edges')
        need(all(0 <= a < b < self.n for a,b in self.edges), 'simple graph edge type')

    def cut(self, block):
        b = tuple(sorted(block))
        return Graph(len(b), tuple((b.index(x), b.index(y)) for x,y in self.edges
                                  if x in b and y in b))

EMPTY, POINT = Graph(0), Graph(1)

def all_graphs(n):
    pairs = tuple(combinations(range(n), 2))
    return tuple(Graph(n, tuple(e for e,x in zip(pairs, flags) if x))
                 for flags in product((0,1), repeat=len(pairs)))

def all_blocks(n, arity):
    for allocation in product(range(arity), repeat=n):
        yield tuple(tuple(v for v,a in enumerate(allocation) if a == i) for i in range(arity))

def validate_blocks(target, path, blocks):
    need(len(path) == len(blocks), 'full occurrence count')
    need(sorted(v for b in blocks for v in b) == list(range(target.n)), 'partition disjoint cover')
    need(all(tuple(sorted(b)) == b for b in blocks), 'subset increasing coordinates')
    need((MUTATION == 'erase_unary_graph_profile' and len(path) == 1) or
         all(target.cut(b) == graph for graph,b in zip(path,blocks)), 'entire induced graph profile')

# ---- Finite groupoid with three interfaces and all S3 automorphisms. ----
PERMS = tuple(permutations(range(3)))
IDP = (0,1,2)

@dataclass(frozen=True)
class Arrow:
    a: int
    b: int
    perm: tuple

    def __post_init__(self):
        need(self.a in range(3) and self.b in range(3) and self.perm in PERMS, 'groupoid arrow type')

def aid(a):
    return Arrow(a,a,IDP)

def acomp(g,f):
    need(f.b == g.a, 'groupoid composition interface')
    return Arrow(f.a,g.b,tuple(g.perm[f.perm[i]] for i in range(3)))

def ainv(f):
    return Arrow(f.b,f.a,tuple(f.perm.index(i) for i in range(3)))

def arrow_path(path, start):
    a = aid(start)
    for h in path:
        a = acomp(h.grade,a)
    return a

@dataclass(frozen=True)
class GH:
    graph: Graph
    grade: Arrow

@dataclass(frozen=True)
class GC:
    path: tuple
    start: int
    target: GH
    left: Arrow
    right: Arrow
    blocks: tuple
    scalar: int

    def __post_init__(self):
        q = arrow_path(self.path,self.start)
        need(self.left.a == self.start and self.right.a == q.b, 'graph cell boundary domains')
        need(self.left.b == self.target.grade.a and self.right.b == self.target.grade.b,
             'graph cell boundary codomains')
        need(acomp(self.target.grade,self.left) == acomp(self.right,q), 'graph cell grade square')
        validate_blocks(self.target.graph,tuple(h.graph for h in self.path),self.blocks)
        need(self.scalar in M, 'graph cell scalar')

def gid(h):
    return GC((h,),h.grade.a,h,aid(h.grade.a),aid(h.grade.b),(tuple(range(h.graph.n)),),0)

def gsub(alpha, row, empty_map=None):
    need(len(row) == len(alpha.path), 'graph substitution exact arity')
    if not row:
        need(empty_map is not None and empty_map.b == alpha.start, 'graph empty row boundary retained')
        return GC((),empty_map.a,alpha.target,acomp(alpha.left,empty_map),
                  acomp(alpha.right,empty_map),(),alpha.scalar)
    need(all(c.target == h for c,h in zip(row,alpha.path)), 'graph substitution full output profile')
    need(all(c.right == d.left for c,d in zip(row,row[1:])), 'graph substitution shared vertical arrows')
    blocks = tuple(tuple(alpha.blocks[i][v] for v in b) for i,c in enumerate(row) for b in c.blocks)
    values = [alpha.scalar] + [c.scalar for c in row if not (MUTATION == 'drop_nullary_scalar' and not c.path)]
    return GC(tuple(h for c in row for h in c.path),row[0].start,alpha.target,
              acomp(alpha.left,row[0].left),acomp(alpha.right,row[-1].right),blocks,scalars(values))

def grestrict(h,f,g):
    need(f.b == h.grade.a and g.b == h.grade.b, 'graph restriction boundaries')
    gi = ainv(g)
    if MUTATION == 'omit_grade_inverse':
        gi = Arrow(g.b,g.a,g.perm)
    r = GH(h.graph,acomp(gi,acomp(h.grade,f)))
    return r,GC((r,),f.a,h,f,g,(tuple(range(h.graph.n)),),0)

def glift(alpha,f,g,u,v):
    need(acomp(f,u) == alpha.left and acomp(g,v) == alpha.right, 'graph lift factoring boundaries')
    r,_ = grestrict(alpha.target,f,g)
    blocks = tuple(sorted(alpha.blocks)) if MUTATION == 'sort_graph_partition' else alpha.blocks
    scalar = 0 if MUTATION == 'erase_graph_scalar' else alpha.scalar
    return GC(alpha.path,alpha.start,r,u,v,blocks,scalar)

def gunit(a):
    h = GH(EMPTY,aid(a))
    return h,GC((),a,h,aid(a),aid(a),(),0)

def gunit_factor(alpha,j):
    a = alpha.start if j == 0 else alpha.path[j-1].grade.b
    h,_ = gunit(a)
    return GC(alpha.path[:j]+(h,)+alpha.path[j:],alpha.start,alpha.target,
              alpha.left,alpha.right,alpha.blocks[:j]+((),)+alpha.blocks[j:],alpha.scalar)

def gcells(path,start,target,left,right):
    if acomp(target.grade,left) != acomp(right,arrow_path(path,start)):
        return
    for bs in all_blocks(target.graph.n,len(path)):
        if (MUTATION == 'erase_unary_graph_profile' and len(path) == 1) or all(target.graph.cut(b) == h.graph for b,h in zip(bs,path)):
            for m in M:
                yield GC(tuple(path),start,target,left,right,bs,m)

def gdirect(graph,blocks,grades,m=0):
    need(len(blocks) == len(grades), 'graph direct profile length')
    start = grades[0].a if grades else 0
    path = tuple(GH(graph.cut(b),h) for b,h in zip(blocks,grades))
    target = GH(graph,arrow_path(path,start))
    return GC(path,start,target,aid(start),aid(target.grade.b),blocks,m)

# ---- Full finite spans, including genuinely noninvertible vertical maps. ----
@dataclass(frozen=True)
class Fn:
    dom: tuple
    cod: tuple
    values: tuple

    def __post_init__(self):
        need(len(self.dom) == len(set(self.dom)) and len(self.cod) == len(set(self.cod)), 'actual finite sets')
        need(len(self.dom) == len(self.values) and all(x in self.cod for x in self.values), 'function typing')

    def __call__(self,x):
        return self.values[self.dom.index(x)]

def fun(dom,cod,rule):
    return Fn(tuple(dom),tuple(cod),tuple(rule(x) for x in dom))

def fid(a):
    return Fn(a,a,a)

def fcomp(g,f):
    need(f.cod == g.dom,'function composite type')
    return fun(f.dom,g.cod,lambda x:g(f(x)))

def functions(a,b):
    return tuple(Fn(a,b,values) for values in product(b,repeat=len(a)))

@dataclass(frozen=True)
class Span:
    left: Fn
    right: Fn

    def __post_init__(self):
        need(self.left.dom == self.right.dom,'span common apex')

    @property
    def A(self): return self.left.cod
    @property
    def B(self): return self.right.cod
    @property
    def E(self): return self.left.dom

@dataclass(frozen=True)
class SH:
    graph: Graph
    span: Span

@lru_cache(None)
def tuples(path,start):
    current = tuple((a,) for a in start)
    endpoint = start
    for h in path:
        need(h.span.A == endpoint,'span full path interfaces')
        current = tuple(z+(e,h.span.right(e)) for z in current for e in h.span.E if h.span.left(e)==z[-1])
        endpoint = h.span.B
    return current

@dataclass(frozen=True)
class SC:
    path: tuple
    start: tuple
    target: SH
    left: Fn
    right: Fn
    blocks: tuple
    coefficient: Fn
    scalar: int

    def __post_init__(self):
        end = self.path[-1].span.B if self.path else self.start
        need((self.left.dom,self.right.dom)==(self.start,end),'span cell boundary domains')
        need((self.left.cod,self.right.cod)==(self.target.span.A,self.target.span.B),'span cell boundary codomains')
        validate_blocks(self.target.graph,tuple(h.graph for h in self.path),self.blocks)
        need(self.coefficient.dom == tuples(self.path,self.start) and self.coefficient.cod == self.target.span.E,
             'span coefficient full tuple domain and apex codomain')
        need(all(self.target.span.left(self.coefficient(z))==self.left(z[0]) and
                 self.target.span.right(self.coefficient(z))==self.right(z[-1]) for z in self.coefficient.dom),
             'span coefficient endpoint equations')
        need(self.scalar in M,'span cell scalar')

def scall(path,start,target,left,right,blocks,rule,m=0):
    p=tuple(path)
    return SC(p,start,target,left,right,tuple(blocks),fun(tuples(p,start),target.span.E,rule),m)

def sid(h):
    return scall((h,),h.span.A,h,fid(h.span.A),fid(h.span.B),(tuple(range(h.graph.n)),),lambda z:z[1])

def ssub(alpha,row,empty_map=None):
    need(len(row)==len(alpha.path),'span substitution exact arity')
    if not row:
        need(empty_map is not None and empty_map.cod==alpha.start,'span empty row boundary retained')
        return scall((),empty_map.dom,alpha.target,fcomp(alpha.left,empty_map),fcomp(alpha.right,empty_map),(),
                     lambda z:alpha.coefficient((empty_map(z[0]),)),alpha.scalar)
    need(all(c.target==h for c,h in zip(row,alpha.path)),'span substitution full output profiles')
    need(all(c.right==d.left for c,d in zip(row,row[1:])),'span substitution shared vertical map')
    p=tuple(h for c in row for h in c.path)
    bs=tuple(tuple(alpha.blocks[i][v] for v in b) for i,c in enumerate(row) for b in c.blocks)
    def evaluate(z):
        image=(row[0].left(z[0]),)
        cursor=0
        for c in row:
            run=z[2*cursor:2*(cursor+len(c.path))+1]
            image+=(c.coefficient(run),c.right(run[-1]))
            cursor+=len(c.path)
        return alpha.coefficient(image)
    return scall(p,row[0].start,alpha.target,fcomp(alpha.left,row[0].left),fcomp(alpha.right,row[-1].right),bs,
                 evaluate,scalars([alpha.scalar]+[c.scalar for c in row]))

def scells(path,start,target,left,right):
    domain=tuples(tuple(path),start)
    fibres=tuple(tuple(e for e in target.span.E if target.span.left(e)==left(z[0]) and
                       target.span.right(e)==right(z[-1])) for z in domain)
    for bs in all_blocks(target.graph.n,len(path)):
        if all(target.graph.cut(b)==h.graph for b,h in zip(bs,path)):
            for values in product(*fibres):
                for m in M:
                    yield SC(tuple(path),start,target,left,right,bs,Fn(domain,target.span.E,values),m)

def srestrict(h,f,g):
    need(f.cod==h.span.A and g.cod==h.span.B,'span restriction boundary type')
    E=tuple((x,e,y) for x in f.dom for e in h.span.E for y in g.dom
            if f(x)==h.span.left(e) and g(y)==h.span.right(e))
    if MUTATION=='drop_pullback_fibre':
        E=E[:-1]
    r=SH(h.graph,Span(fun(E,f.dom,lambda z:z[0]),fun(E,g.dom,lambda z:z[2])))
    return r,scall((r,),f.dom,h,f,g,(tuple(range(h.graph.n)),),lambda z:z[1][1])

def slift(alpha,f,g,u,v):
    need(fcomp(f,u)==alpha.left and fcomp(g,v)==alpha.right,'span lift factoring boundaries')
    r,_=srestrict(alpha.target,f,g)
    return scall(alpha.path,alpha.start,r,u,v,alpha.blocks,
                 lambda z:(u(z[0]),alpha.coefficient(z),v(z[-1])),alpha.scalar)

def sunit(a):
    u=SH(EMPTY,Span(fid(a),fid(a)))
    return u,scall((),a,u,fid(a),fid(a),(),lambda z:z[0])

def sunit_factor(alpha,j):
    a=alpha.start if j==0 else alpha.path[j-1].span.B
    u,_=sunit(a)
    p=alpha.path[:j]+(u,)+alpha.path[j:]
    bs=alpha.blocks[:j]+((),)+alpha.blocks[j:]
    def rule(z):
        k=2*j
        return alpha.coefficient(z[:k+1]+z[k+3:])
    return scall(p,alpha.start,alpha.target,alpha.left,alpha.right,bs,rule,alpha.scalar)

# Canonical regular representation: actual tagged arrows into each object.
@lru_cache(None)
def regular(a):
    return tuple((i,a,p) for i in range(3) for p in PERMS)

@lru_cache(None)
def fmap(h):
    return fun(regular(h.a),regular(h.b),lambda x:(x[0],h.b,tuple(h.perm[x[2][i]] for i in range(3))))

@lru_cache(None)
def embed_h(h):
    f=fmap(h.grade)
    return SH(h.graph,Span(fid(f.dom),f))

def embed_cell(c):
    p=tuple(embed_h(h) for h in c.path)
    m=0 if MUTATION=='forget_comparison_scalar' else c.scalar
    return scall(p,regular(c.start),embed_h(c.target),fmap(c.left),fmap(c.right),c.blocks,
                 lambda z:fmap(c.left)(z[0]),m)

def refinement_key(row):
    if MUTATION=='forget_refinement_slots':
        return frozenset(row)
    return tuple(row)

# ---- Independent finite checks: explicit equalities and enumerated fibres. ----
def test_groupoid():
    arrows=tuple(Arrow(a,b,p) for a,b,p in product(range(3),range(3),PERMS))
    for f in arrows:
        need(acomp(ainv(f),f)==aid(f.a) and acomp(f,ainv(f))==aid(f.b),'groupoid inverse equations')
        COUNT['groupoid_inverse_equations']+=2
    for a,b,c,d in product(range(3),repeat=4):
        for pf,pg,ph in product(PERMS,repeat=3):
            f,g,h=Arrow(a,b,pf),Arrow(b,c,pg),Arrow(c,d,ph)
            need(acomp(h,acomp(g,f))==acomp(acomp(h,g),f),'groupoid associativity')
            COUNT['groupoid_associativity_equations']+=1
    # All endpoint object combinations and S3 grades: inverse sensitivity is real.
    for a,b,x,y in product(range(3),repeat=4):
        for ph,pf,pg in product(PERMS,repeat=3):
            h=GH(POINT,Arrow(a,b,ph)); f=Arrow(x,a,pf); g=Arrow(y,b,pg)
            r,k=grestrict(h,f,g)
            need(acomp(g,r.grade)==acomp(h.grade,f),'g inverse h f cartesian square')
            need(glift(k,f,g,aid(x),aid(y))==gid(r),'graph cartesian eta identity')
            COUNT['graph_restriction_grade_cases']+=1
    # Noncommuting composable changes at every interface, with full witness coordinates.
    for perms in product(PERMS,repeat=4):
        f,g,u,v=Arrow(1,0,perms[0]),Arrow(2,1,perms[1]),Arrow(2,1,perms[2]),Arrow(0,2,perms[3])
        h=GH(Graph(2,((0,1),)),Arrow(0,1,(1,2,0)))
        r,k=grestrict(h,f,g); rr,kk=grestrict(r,u,v)
        rd,kd=grestrict(h,acomp(f,u),acomp(g,v))
        need(rr==rd and gsub(k,(kk,))==kd,'two successive graph restrictions strict coherence')
        COUNT['graph_composable_change_equations']+=1

def test_graph_cells():
    grades=(Arrow(0,1,(1,2,0)),Arrow(1,1,(1,0,2)),Arrow(1,2,(2,0,1)))
    for n in range(4):
        for graph in all_graphs(n):
            for arity in range(4):
                gs=grades[:arity]
                if arity==0:
                    if n: continue
                    c=GC((),0,GH(EMPTY,aid(0)),aid(0),aid(0),(),0)
                    candidates=(replace(c,scalar=m) for m in M)
                else:
                    candidates=(gdirect(graph,bs,gs,m) for bs in all_blocks(n,arity) for m in M)
                for c in candidates:
                    f=Arrow(2,c.target.grade.a,(1,2,0));g=Arrow(0,c.target.grade.b,(2,1,0))
                    u=acomp(ainv(f),c.left);v=acomp(ainv(g),c.right)
                    beta=glift(c,f,g,u,v); r,k=grestrict(c.target,f,g)
                    need(gsub(k,(beta,))==c,'graph restriction beta retains partition/scalar')
                    need(glift(gsub(k,(beta,)),f,g,u,v)==beta,'graph restriction eta retains full witness')
                    # Enumerated entire factor fibre, not existence alone.
                    fibre=tuple(b for b in gcells(c.path,c.start,r,u,v) if gsub(k,(b,))==c)
                    need(fibre==(beta,),'graph unique actual lift fibre')
                    need(gsub(gid(c.target),(c,))==c,'graph left identity')
                    if c.path: need(gsub(c,tuple(gid(h) for h in c.path))==c,'graph right identities')
                    for j in range(arity+1):
                        fact=gunit_factor(c,j); row=[gid(h) for h in c.path]
                        row.insert(j,gunit(fact.path[j].grade.a)[1])
                        need(gsub(fact,tuple(row))==c,'graph contextual unit beta')
                        need(gunit_factor(gsub(fact,tuple(row)),j)==fact,'graph contextual unit eta')
                        COUNT['graph_contextual_unit_factor_cells']+=1
                    COUNT['graph_actual_cartesian_fibres']+=1

def test_span_fibres():
    one=(0,); two=(0,1); empty=(); E=('x','y')
    spans=(Span(fun(E,one,lambda _:0),fun(E,one,lambda _:0)),
           Span(fun(E,two,lambda e:E.index(e)),fun(E,two,lambda _:0)),
           Span(fun(empty,two,lambda _:0),fun(empty,one,lambda _:0)))
    for S in spans:
        for X,Y in product((empty,one,two),repeat=2):
            for f,g in product(functions(X,S.A),functions(Y,S.B)):
                for graph in (EMPTY,POINT):
                    h=SH(graph,S);r,k=srestrict(h,f,g)
                    # All actual cells on unary and surrounding empty-graph profiles.
                    paths=[(r,)]
                    if X==Y:
                        u=sunit(X)[0];paths.extend(((u,r),(r,u)))
                        if graph==EMPTY: paths.append(())
                    for p in paths:
                        all_factors=tuple(scells(p,X,r,fid(X),fid(Y)))
                        direct_targets=set(scells(p,X,h,f,g))
                        images=tuple(ssub(k,(beta,)) for beta in all_factors)
                        need(len(images)==len(set(images)) and set(images)==direct_targets,
                             'span cartesian enumerated full source and target fibre bijection')
                        COUNT['span_entire_cartesian_fibre_bijections']+=1
                        for beta in all_factors:
                            alpha=ssub(k,(beta,));actual=slift(alpha,f,g,fid(X),fid(Y))
                            need(actual==beta and ssub(k,(actual,))==alpha,'span cartesian beta eta actual cells')
                            COUNT['span_actual_cartesian_factor_cells']+=1
                    COUNT['span_restriction_profiles']+=1
                    if len(set(f.values))<len(f.dom) or len(set(g.values))<len(g.dom):
                        COUNT['noninvertible_vertical_restrictions']+=1
    # All nullary/unary/binary cells into a span with two actual witnesses.
    q=SH(EMPTY,spans[0]); idone=fid(one)
    for arity in range(4):
        for alpha in scells((q,)*arity,one,q,idone,idone):
            for j in range(arity+1):
                fact=sunit_factor(alpha,j);row=[sid(h) for h in alpha.path];row.insert(j,sunit(one)[1])
                need(ssub(fact,tuple(row))==alpha,'span contextual unit beta')
                need(sunit_factor(ssub(fact,tuple(row)),j)==fact,'span contextual unit eta')
                for k in range(arity+1):
                    lhs=sunit_factor(sunit_factor(alpha,j),k+(k>=j))
                    rhs=sunit_factor(sunit_factor(alpha,k),j+(j>k))
                    need(lhs==rhs,'span two contextual unit insertion coherence')
                    COUNT['span_two_unit_context_coherences']+=1
                COUNT['span_contextual_unit_factor_cells']+=1
    # Two genuinely noninvertible changes; compare actual lifted cells, not apex counts.
    S=SH(POINT,spans[0]); f=fun(two,one,lambda _:0); g=f
    r,k=srestrict(S,f,g)
    for u,v in product(functions(two,two),repeat=2):
        rr,kk=srestrict(r,u,v);rd,kd=srestrict(S,fcomp(f,u),fcomp(g,v))
        combined=ssub(k,(kk,));comparison=slift(combined,fcomp(f,u),fcomp(g,v),fid(two),fid(two))
        need(ssub(kd,(comparison,))==combined,'span successive restriction comparison square')
        expected=tuple((z[1][0],z[1][1][1],z[1][2]) for z in comparison.coefficient.dom)
        need(comparison.coefficient.values==expected,'span nested pullback flattening exact apex coordinates')
        COUNT['span_composable_change_factor_equations']+=1
    # Noninjective unit pullback is not its source diagonal universal unit.
    pulled,_=srestrict(sunit(one)[0],f,f)
    need(len(pulled.span.E)==4 and len(sunit(two)[0].span.E)==2,'noninvertible unit pullback is not diagonal unit')


def test_comparison_and_refinement():
    edges=((0,1),(1,2),(1,3),(2,4),(3,4),(4,5))
    G=Graph(6,edges); Gplus=Graph(6,tuple(sorted(edges+((0,5),))))
    bs=((0,),(1,3),(2,4),(5,))
    grades=(Arrow(0,1,(1,0,2)),aid(1),aid(1),Arrow(1,2,(0,2,1)))
    c=gdirect(G,bs,grades,1);d=gdirect(Gplus,bs,grades,1)
    need(c.path==d.path and c.target!=d.target and c!=d,'principal N6 nonreconstructive wholes retained')
    need(c.path[1]==c.path[2] and c.path[1].graph.n==2,'literally repeated nonempty components')
    first=gdirect(c.path[1].graph,((0,),(1,)),(aid(1),aid(1)),0)
    second=gdirect(c.path[2].graph,((1,),(0,)),(aid(1),aid(1)),0)
    need(first.path==second.path and first.target==second.target and first!=second,'distinct parallel actual local refinements')
    row=(gid(c.path[0]),first,second,gid(c.path[3]))
    composed=gsub(c,row)
    need(composed.blocks==((0,),(1,),(3,),(4,),(2,),(5,)),'principal ambient refinement blocks exact')
    swapped=(row[0],second,first,row[3])
    need(refinement_key(row)!=refinement_key(swapped),'ordered occurrence refinement family retained')
    need(gsub(c,row)!=gsub(c,swapped),'opposite repeated refinements do not collapse')
    need(embed_cell(gsub(c,row))==ssub(embed_cell(c),tuple(embed_cell(x) for x in row)),
         'graph to full Span preserves actual substitution')
    need(embed_cell(c).scalar==c.scalar and embed_cell(c).blocks==c.blocks,'comparison retains scalar and partition')
    need(embed_cell(c).target!=embed_cell(d).target,'comparison reflects whole inequality')
    # Coefficient is unique on every original profile; enumerate all Span cells.
    for graph in all_graphs(2):
        for blocks in all_blocks(2,2):
            for m in M:
                original=gdirect(graph,blocks,(grades[0],grades[3]),m)
                image=embed_cell(original)
                fibre=set(scells(image.path,image.start,image.target,image.left,image.right))
                expected={embed_cell(x) for x in gcells(original.path,original.start,original.target,original.left,original.right)}
                need(fibre==expected,'comparison surjective on entire original cell profile')
                need(len(expected)==len(tuple(gcells(original.path,original.start,original.target,original.left,original.right))),
                     'comparison reflects witness equality on entire original cell profile')
                COUNT['comparison_original_profile_bijections']+=1
    # Scalar-paired parallel refinement arrows with equal composites remain distinct.
    aa=(replace(gid(c.path[1]),scalar=0),replace(gid(c.path[2]),scalar=0))
    bb=(replace(gid(c.path[1]),scalar=1),replace(gid(c.path[2]),scalar=1))
    need(aa!=bb and scalars(x.scalar for x in aa)==scalars(x.scalar for x in bb),'parallel scalar refinement arrows retained')
    need(tuple(map(embed_cell,aa))!=tuple(map(embed_cell,bb)),'comparison reflects full refinement tuples')
    COUNT['principal_N6_full_witness_regressions']+=12


def test_substitution_and_normal_comparison():
    # Nontrivial graph partitions in three rows, including an empty inner run.
    graph=Graph(3,((0,1),(1,2)))
    outer=gdirect(graph,((0,1),(2,)),(aid(0),aid(0)),1)
    mid=(gdirect(outer.path[0].graph,((1,),(0,)),(aid(0),aid(0)),1),
         gdirect(POINT,((),(0,)),(aid(0),aid(0)),2))
    bottom=((gid(mid[0].path[0]),gid(mid[0].path[1])),
            (GC((),0,gunit(0)[0],aid(0),aid(0),(),1),gid(mid[1].path[1])))
    lhs=gsub(gsub(outer,mid),tuple(c for row in bottom for c in row))
    rhs=gsub(outer,tuple(gsub(c,row) for c,row in zip(mid,bottom)))
    need(lhs==rhs,'graph three-row substitution includes actual empty inner run')
    need(embed_cell(lhs)==ssub(ssub(embed_cell(outer),tuple(map(embed_cell,mid))),
                              tuple(embed_cell(c) for row in bottom for c in row)),
         'normal comparison preserves full three-row witness')
    COUNT['graph_three_row_substitution_equalities']+=2
    # Full Span coefficient functions vary independently, not just graph-span images.
    A=(0,);E=(0,1);q=SH(EMPTY,Span(fun(E,A,lambda _:0),fun(E,A,lambda _:0)))
    identity=fid(A)
    outs=tuple(scells((q,q),A,q,identity,identity))
    for outer in outs:
        for s,t,u in product(M,repeat=3):
            left=scall((),A,q,identity,identity,(),lambda _:1,s)
            right=scall((q,q),A,q,identity,identity,((),()),lambda z:(z[1]+z[3])%2,t)
            children=(replace(sid(q),scalar=u),scall((q,),A,q,identity,identity,((),),lambda z:1-z[1],1))
            lhs=ssub(ssub(outer,(left,right)),children)
            rhs=ssub(outer,(ssub(left,(),empty_map=identity),ssub(right,children)))
            need(lhs==rhs,'Span three-row coefficient substitution with nullary run')
            COUNT['span_three_row_substitution_equalities']+=1
    # J preserves chosen restrictions by an actual invertible cartesian comparison,
    # not a false literal equality of graph-of-function and triple pullback apexes.
    for ph,pf,pg in product(PERMS,repeat=3):
        h=GH(POINT,Arrow(0,1,ph));f=Arrow(2,0,pf);g=Arrow(0,1,pg)
        r,k=grestrict(h,f,g); Jh,Jr=embed_h(h),embed_h(r)
        rspan,kspan=srestrict(Jh,fmap(f),fmap(g))
        comparison=slift(embed_cell(k),fmap(f),fmap(g),fid(regular(2)),fid(regular(0)))
        inverse=scall((rspan,),regular(2),Jr,fid(regular(2)),fid(regular(0)),((0,),),lambda z:z[1][0])
        need(ssub(kspan,(comparison,))==embed_cell(k),'normal comparison restriction factor equation')
        need(ssub(inverse,(comparison,))==sid(Jr),'normal comparison restriction left inverse')
        need(ssub(comparison,(inverse,))==sid(rspan),'normal comparison restriction right inverse')
        COUNT['normal_comparison_cartesian_isomorphism_equations']+=3
    for a in range(3):
        need(embed_h(gunit(a)[0])==sunit(regular(a))[0] and embed_cell(gunit(a)[1])==sunit(regular(a))[1],
             'normal comparison preserves actual chosen universal unit')
        COUNT['normal_comparison_unit_equalities']+=2


def test_exact_and_nonrepresentable():
    one=(0,); e=('x','y');idone=fid(one)
    basic=Span(fun(e,one,lambda _:0),fun(e,one,lambda _:0))
    # Positive assembly with nontrivial two-witness coefficients and one nonempty graph.
    a=SH(POINT,basic);b=SH(EMPTY,basic);path=(a,b)
    P=tuples(path,one)
    composite=SH(POINT,Span(fun(P,one,lambda z:z[0]),fun(P,one,lambda z:z[-1])))
    k=scall(path,one,composite,idone,idone,((0,),()),lambda z:z)
    target=SH(POINT,basic)
    for alpha in scells(path,one,target,idone,idone):
        def rule(z): return alpha.coefficient(z[1])
        factor=scall((composite,),one,target,idone,idone,((0,),),rule,alpha.scalar)
        need(ssub(factor,(k,))==alpha,'positive Span assembly actual factor equation')
        actual=tuple(x for x in scells((composite,),one,target,idone,idone) if ssub(x,(k,))==alpha)
        need(actual==(factor,),'positive Span assembly unique actual factor fibre')
        COUNT['positive_exact_assembly_fibres']+=1
    # Contextual positive assembly with two-sided nonempty surrounding maps.
    outer=scall((b,composite,b),one,target,idone,idone,((),(0,),()),lambda z:e[(len(z[3])+z[1].count('x'))%2],1)
    expanded=ssub(outer,(sid(b),k,sid(b)))
    # Expanding an apex tuple shares boundary endpoints once.
    def full(z): return z[:3]+z[3][1:]+z[5:]
    recovered=scall(outer.path,one,target,idone,idone,outer.blocks,lambda z:expanded.coefficient(full(z)),expanded.scalar)
    need(recovered==outer,'positive exact assembly arbitrary surrounding tuple context')
    COUNT['positive_exact_context_inverse_equations']+=1
    # Arbitrary scalar-zero unary witnesses are legitimate but not opcartesian.
    zero=replace(sid(a),scalar=2);x=sid(a);y=replace(x,scalar=1)
    need(x!=y and ssub(x,(zero,))==ssub(y,(zero,)),'nonunit scalar actual nonunique assembly factors')
    COUNT['nonuniversal_actual_factor_collisions']+=1
    # True universal nullary versus arbitrary nullary scalar-zero primitive.
    eta=sunit(one)[1];bad=replace(eta,scalar=2);u=sunit(one)[0]
    x=sid(u);y=replace(x,scalar=1)
    need(ssub(x,(bad,))==ssub(y,(bad,)) and x!=y,'nonuniversal nullary primitive is not chosen universal unit')
    COUNT['nonuniversal_nullary_factor_collisions']+=1
    # Genuine path obstruction in unchanged graph universe: both cross-edge wholes.
    point=GH(POINT,aid(0));p=(point,point)
    q0=gdirect(Graph(2),((0,),(1,)),(aid(0),aid(0)))
    q1=gdirect(Graph(2,((0,1),)),((0,),(1,)),(aid(0),aid(0)))
    need(q0.path==p==q1.path and q0.target!=q1.target,'same genuine path has distinct cross-edge wholes')
    for graph in all_graphs(2):
        for grade in PERMS:
            candidate=GH(graph,Arrow(0,0,grade))
            source_cells=tuple(gcells(p,0,candidate,aid(0),aid(0)))
            if not source_cells: continue
            both=bool(tuple(gcells((candidate,),0,q0.target,aid(0),aid(0)))) and bool(tuple(gcells((candidate,),0,q1.target,aid(0),aid(0))))
            need(not both,'nonrepresentability: no candidate whole factors both actual target cells')
            COUNT['nonrepresentable_candidate_whole_graphs']+=1
    # A cut with two nonempty inputs is nonopcartesian even with unit scalar.
    need(not tuple(gcells((q0.target,),0,q1.target,aid(0),aid(0))),
         'legitimate graph cut misses alternate cross-edge target factor')
    # Forgetting graph data collapses these cells: not a faithful whole comparison.
    need(embed_cell(q0).target.span==embed_cell(q1).target.span,'graph-forgetting comparison demonstrably loses wholes')
    COUNT['graph_forgetting_information_loss']+=1


def sentinels():
    h=GH(POINT,Arrow(0,1,(1,2,0)));f=Arrow(2,0,IDP);g=Arrow(2,1,(1,2,0))
    grestrict(h,f,g)  # inverse mutation must fail in actual cell constructor
    c=gdirect(Graph(2),((1,),(0,)),(aid(0),aid(0)),1)
    b=glift(c,aid(0),aid(0),aid(0),aid(0))
    need(gsub(grestrict(c.target,aid(0),aid(0))[1],(b,))==c,'sentinel graph full witness lift')
    need(embed_cell(c).scalar==c.scalar,'sentinel comparison scalar reflection')
    x,y=replace(gid(c.path[0]),scalar=0),replace(gid(c.path[0]),scalar=1)
    need(refinement_key((x,y))!=refinement_key((y,x)),'sentinel ordered refinement slots')
    binary=gdirect(EMPTY,((),()),(aid(0),aid(0)),0)
    nullary=GC((),0,gunit(0)[0],aid(0),aid(0),(),1)
    need(gsub(binary,(nullary,gid(binary.path[1]))).scalar==1,'sentinel nullary scalar retained')
    A=(0,1);B=(0,);f=fun(A,B,lambda _:0);u=sunit(B)[0]
    r,k=srestrict(u,f,f)
    need(len(r.span.E)==4,'sentinel full noninjective pullback fibre')

MUTATIONS=('omit_grade_inverse','sort_graph_partition','erase_graph_scalar','drop_nullary_scalar',
           'forget_comparison_scalar','forget_refinement_slots','drop_pullback_fibre','erase_unary_graph_profile')

def main():
    global MUTATION
    p=argparse.ArgumentParser();p.add_argument('--mutate',choices=MUTATIONS)
    p.add_argument('--expect-optimize',type=int,choices=(0,1,2));args=p.parse_args();MUTATION=args.mutate
    try:
        need(args.expect_optimize is None or sys.flags.optimize==args.expect_optimize,'interpreter optimization mode mismatch')
        sentinels()
        for test in (test_groupoid,test_graph_cells,test_span_fibres,test_comparison_and_refinement,test_substitution_and_normal_comparison,test_exact_and_nonrepresentable):
            test()
        result={'status':'PASS','fixture':{'groupoid_objects':3,'automorphisms_per_object':6,
                 'scalar_monoid':'C2 with absorbing zero','principal_graph_bound':6},'counts':dict(sorted(COUNT.items())),
                'scope':'bounded actual-cell evidence; parameterized universal properties remain P; typed core separately checked'}
        code=0
    except (Failure,ValueError,IndexError) as error:
        result={'status':'REJECT','mutation':MUTATION,'reason':str(error)};code=1
    print(json.dumps(result,sort_keys=True))
    return code

if __name__=='__main__':
    raise SystemExit(main())
