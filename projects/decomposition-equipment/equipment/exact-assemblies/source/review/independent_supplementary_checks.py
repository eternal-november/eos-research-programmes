#!/usr/bin/env python3
"""Independent finite probes. Imports frozen primitives, not their test verdicts."""
from pathlib import Path
from itertools import product
from dataclasses import replace
from collections import Counter
import importlib.util, sys, json, hashlib, argparse
parser=argparse.ArgumentParser();parser.add_argument('--source-root',type=Path,default=Path(__file__).resolve().parents[1]);args=parser.parse_args()
ROOT=args.source_root.resolve()
spec=importlib.util.spec_from_file_location('independent_e5',ROOT/'checks/e5_exact_cells.py')
q=importlib.util.module_from_spec(spec);sys.modules[spec.name]=q;spec.loader.exec_module(q)
e=q.e; w=q.w
counts=Counter()
def need(ok, why):
    if not ok: raise RuntimeError(why)
def raw_tuples(path,start):
    if not path:return tuple((a,) for a in start)
    out=[]
    for xs in product(*(h.span.E for h in path)):
        if all(path[i].span.right(xs[i])==path[i+1].span.left(xs[i+1]) for i in range(len(path)-1)):
            z=(path[0].span.left(xs[0]),)
            for h,x in zip(path,xs): z+=(x,h.span.right(x))
            out.append(z)
    return tuple(out)
def raw_restrict(h,f,g):
    rows=tuple(((a,x,b),a,b) for a in f.dom for x in h.span.E for b in g.dom
               if f(a)==h.span.left(x) and g(b)==h.span.right(x))
    return q.span(f.dom,g.dom,rows,h.word)
def direct_comparison(path,fs):
    actual,report=q.comparison(path,fs)
    restricted=tuple(raw_restrict(h,f,g) for h,f,g in zip(path,fs,fs[1:]))
    source=raw_tuples(restricted,fs[0].dom)
    old=raw_tuples(path,fs[0].cod)
    target=tuple((a,z,b) for a in fs[0].dom for z in old for b in fs[-1].dom if fs[0](a)==z[0] and fs[-1](b)==z[-1])
    table={}
    for z in source:
        image=(fs[0](z[0]),)
        for i in range(len(path)):image+=(z[2*i+1][1],fs[i+1](z[2*i+2]))
        table[z]=(z[0],image,z[-1])
    need(set(actual.coefficient.dom)==set(source),'raw independent source tuples')
    need(set(actual.coefficient.cod)==set(target),'raw independent target tuples')
    need(dict(zip(actual.coefficient.dom,actual.coefficient.values))==table,'raw independent complete comparison table')
    fibres={y:sum(v==y for v in table.values()) for y in target}
    need(q.bijective(actual.coefficient)==all(v==1 for v in fibres.values()),'independent per-target witness reconstruction')
    counts['mixed_exterior_and_internal_actual_comparison_tables']+=1
    counts['independently_checked_target_witnesses']+=len(target)
    return actual
A=(0,1);patterns=((1,0),(0,0,1),(0,),())
full=q.span(A,A,((('full',a,b),a,b) for a,b in product(A,repeat=2)))
duplicate=q.span(A,A,((('duplicate',a,b,j),a,b) for a,b in product(A,repeat=2) for j in (0,1)))
for h in (full,duplicate):
    for n in (2,3,4):
        exterior=((a,b) for a in patterns for b in patterns) if n==2 else ((patterns[0],patterns[1]),(patterns[2],patterns[0]),(patterns[3],patterns[1]))
        for left,right in exterior:
            for internals in product(patterns,repeat=n-1):
                fs=tuple(q.finite_map(v,A) for v in (left,*internals,right))
                direct_comparison((h,)*n,fs)
# Nonempty and empty graph occurrences are not erased by transport/contraction.
words=((e.POINT,),(e.EMPTY,),(),(e.Graph(2,((0,1),)),))
for n in (3,4):
    leaves=tuple(replace(full,word=words[i]) for i in range(n))
    for shape in q.shapes(n):
        tree=q.build(shape,leaves,[0]);old=q.flatten_tree(tree)
        for internals in product(patterns[:3],repeat=n-1):
            fs=(q.finite_map((0,0,1),A),)+tuple(q.finite_map(v,A) for v in internals)+(q.finite_map((1,0),A),)
            transported=q.flatten_tree(q.transport_tree(tree,fs))
            need(transported.coefficient==q.independent_full_transport(tree,fs),'mixed-chart nonempty-word tree table')
            need(transported.forest==old.forest,'actual graph words and empty occurrences retained')
            need(transported.scalar==old.scalar,'mixed-chart tree scalar retained')
            for name in q.internal_names(tree)[1:]:
                got=q.flatten_tree(q.transport_tree(q.contract(tree,name),fs))
                need(got==transported,'nonempty-word single-node contraction equality')
                counts['labelled_tree_contraction_equalities']+=1
            counts['labelled_mixed_chart_tree_tables']+=1
# Independent singleton active-root/inactive-proper-node witness.
ONE=(0,);one=e.Span(e.fun(('x',),ONE,lambda _:0),e.fun(('x',),ONE,lambda _:0))
point=e.SH(e.POINT,one);proper=e.SH(e.Graph(2),one);whole=e.SH(e.Graph(3,((0,2),)),one)
proper_cell=e.scall((point,point),ONE,proper,e.fid(ONE),e.fid(ONE),((0,),(1,)),lambda z:'x')
outer=e.scall((proper,point),ONE,whole,e.fid(ONE),e.fid(ONE),((0,1),(2,)),lambda z:'x')
flat=e.ssub(outer,(proper_cell,e.sid(point)))
need(flat.target.graph.cut((0,1))==proper.graph and not proper.graph.edges and bool(whole.graph.edges),'edge activity retained at proper and root graphs')
h=q.span(ONE,ONE,(('x',0,0),));dup=q.finite_map((0,0),ONE);ident=e.fid(ONE)
proper_cmp=direct_comparison((h,h),(ident,dup,ident));root_cmp=direct_comparison((h,h,h),(ident,dup,ident,ident))
need(not q.bijective(proper_cmp.coefficient) and q.histogram(proper_cmp.coefficient)==(2,),'inactive proper comparison genuinely two to one')
need({(z[0],z[-1]) for z in root_cmp.coefficient.dom}=={(z[0],z[-1]) for z in root_cmp.coefficient.cod},'active root endpoint supports equal despite failed actual witness comparison')
def quotient_equal(x,y):
    profile=(x.path,x.start,x.target,x.left,x.right,x.blocks,x.scalar)
    other=(y.path,y.start,y.target,y.left,y.right,y.blocks,y.scalar)
    return profile==other and (bool(x.target.graph.edges) or x.coefficient==y.coefficient)
def actual_inverse_attempt(comparison,graph):
    f=comparison.coefficient
    carrier=lambda X:e.SH(graph,e.Span(e.fun(X,ONE,lambda _:0),e.fun(X,ONE,lambda _:0)))
    source=carrier(f.dom);target=carrier(f.cod);block=(tuple(range(graph.n)),)
    forward=e.scall((source,),ONE,target,ident,ident,block,lambda z:f(z[1]))
    reverse=e.scall((target,),ONE,source,ident,ident,block,lambda z:next(x for x in f.dom if f(x)==z[1]))
    return (e.ssub(reverse,(forward,)),e.sid(source),e.ssub(forward,(reverse,)),e.sid(target))
root_back,root_id,root_forward,target_id=actual_inverse_attempt(root_cmp,whole.graph)
need(root_back!=root_id and quotient_equal(root_back,root_id) and quotient_equal(root_forward,target_id),
     'active-root inverse represented by actual two directional maps and checked quotient composites')
proper_back,proper_id,proper_forward,proper_target_id=actual_inverse_attempt(proper_cmp,proper.graph)
need(not quotient_equal(proper_back,proper_id) and quotient_equal(proper_forward,proper_target_id),
     'same actual section does not invert inactive proper map')
counts['active_root_inactive_proper_counterexamples']=1
# Square-zero scalar quotient preserving literal 1 and units, but not fixed-endpoint lifting.
M=('1','a','0')
def mul(x,y):
    if x=='1':return y
    if y=='1':return x
    return '0'
classes=(frozenset(('1',)),frozenset(('a','0')))
def eq(x,y):return any(x in b and y in b for b in classes)
for x,y,z in product(M,repeat=3):
    need(not eq(x,y) or eq(mul(x,z),mul(y,z)),'square-zero scalar quotient congruence')
for b in classes:
    need(len({x=='1' for x in b})==1,'literal identity mark descends in square-zero quotient')
    need(len({any(mul(x,y)=='1' for y in M) for x in b})==1,'unit mark descends in square-zero quotient')
identity_class=next(b for b in classes if '1' in b)
need(eq('a','0') and not any(mul('a',h)=='0' for h in identity_class),'fixed endpoint refinement lift genuinely absent')
counts['square_zero_congruence_and_lifting_boundary']=1
result={'status':'PASS','schema':'E5 independent supplementary finite probes v1','counts':dict(counts),'limits':['Finite supplements reuse frozen E3/E4 primitives and E5 transport functions; raw comparison oracle independently enumerates tuple sets and every coefficient-table entry.','Mixed-chart tree probes cover nonempty/empty graph words, arities 3 and 4 via binary trees and single proper-node contractions, not all finite diagrams.','The active/inactive graph witness and square-zero scalar table are finite diagnostics, not full presentation-kernel proofs.']}
print(json.dumps(result,sort_keys=True,indent=2))
