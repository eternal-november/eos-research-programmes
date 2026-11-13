#!/usr/bin/env python3
"""Non-author C1 audit. No imports from author code or stored author results.

Independent representation: Boolean adjacency matrices, vertex-to-slot words,
and explicitly typed arrow triples. Breadth-three shapes are recursively
generated as plane trees, not author arity vectors. Full product mode executes
both substitution orders for every graph/shape/label/interface-chain case.
"""
from __future__ import annotations
from collections import Counter
from dataclasses import dataclass
from functools import lru_cache
from itertools import product
from math import comb
from pathlib import Path
import argparse, hashlib, json, sys, time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]

def check(ok, message='independent assertion failed'):
    if not ok:
        raise ValueError(message)

@lru_cache(None)
def induced(matrix, vertices):
    return tuple(tuple(matrix[u][v] for v in vertices) for u in vertices)

def graph(m, edges):
    pairs = {frozenset(e) for e in edges}
    return tuple(tuple(i != j and frozenset((i,j)) in pairs for j in range(m)) for i in range(m))

def all_graphs(m):
    # Enumerate row-wise upper triangles; no edge-mask author representation.
    cells = [(i,j) for j in range(m) for i in range(j)]
    for word in product((False,True),repeat=len(cells)):
        yield graph(m,[cell for cell,bit in zip(cells,word) if bit])

def words(length, alphabet):
    # Recursive generation retains the unique zero-length word even at arity 0.
    if length == 0:
        yield ()
    else:
        for rest in words(length-1,alphabet):
            for letter in range(alphabet):
                yield rest+(letter,)

def chains(length):
    # Enumerate arbitrary interface words then test order independently.
    return tuple(w for w in product(range(3),repeat=length)
                 if all(a<=b for a,b in zip(w,w[1:])))

def arrows(chain):
    return tuple((a,b,0) for a,b in zip(chain,chain[1:]))

@dataclass(frozen=True)
class Cut:
    matrix: tuple
    grade: tuple
    arity: int
    word: tuple
    arrows: tuple

def valid(w):
    a,b,e=w.grade
    if not (0<=a<=b<=2 and e in (0,1)): return False
    m=len(w.matrix)
    if len(w.word)!=m or w.arity!=len(w.arrows): return False
    if any(not 0<=x<w.arity for x in w.word): return False
    if any(len(row)!=m for row in w.matrix): return False
    if any(w.matrix[i][i] or w.matrix[i][j]!=w.matrix[j][i] for i in range(m) for j in range(m)): return False
    current=a; total=0
    for x,y,bit in w.arrows:
        if not (x==current and 0<=x<=y<=2 and bit in (0,1)): return False
        current=y;total=(total+bit)%2
    return current==b and total==e

def make(matrix, word, path, grade=None):
    if grade is None:
        check(bool(path),'use explicit grade for nullary')
        grade=(path[0][0],path[-1][1],sum(a[2] for a in path)%2)
    w=Cut(matrix,grade,len(path),tuple(word),tuple(path))
    check(valid(w),'invalid independently constructed cut')
    return w

@lru_cache(None)
def leaf_components(w):
    return tuple((induced(w.matrix,tuple(v for v,x in enumerate(w.word) if x==i)),a)
                 for i,a in enumerate(w.arrows))

def identity(component):
    g,a=component
    return make(g,(0,)*len(g),(a,),a)

def subst(w, forest):
    check(len(forest)==w.arity,'forest occurrence count')
    check(tuple((v.matrix,v.grade) for v in forest)==leaf_components(w),'forest graph/grade typing')
    # Scan the parent word once: seen[i] is this vertex's canonical local rank.
    seen=[0]*w.arity; offsets=[]; size=0
    for f in forest:
        offsets.append(size);size+=f.arity
    output=[]
    for i in w.word:
        output.append(offsets[i]+forest[i].word[seen[i]])
        seen[i]+=1
    arr=tuple(a for f in forest for a in f.arrows)
    result=Cut(w.matrix,w.grade,size,tuple(output),arr)
    check(valid(result),'substitution validity')
    return result

def ambient_blocks(w):
    return tuple(tuple(v for v,x in enumerate(w.word) if x==i) for i in range(w.arity))

def from_blocks(g, blocks, arr, grade=None):
    owner=[None]*len(g)
    for i,b in enumerate(blocks):
        for v in b:
            check(0<=v<len(g) and owner[v] is None,'overlap/out of range')
            owner[v]=i
    check(all(v is not None for v in owner),'missing vertex')
    check(len(blocks)==len(arr),'block arity')
    return make(g,tuple(owner),arr,grade)

def rejected(f):
    try: f()
    except (ValueError,IndexError): return True
    return False

def six_vertex():
    E=((0,1),(1,2),(1,3),(2,4),(3,4),(4,5))
    G=graph(6,E); Bs=((0,),(1,3),(2,4),(5,)); path=(0,1,1,1,2)
    w=from_blocks(G,Bs,arrows(path)); leaves=leaf_components(w)
    check(leaves[1]==leaves[2]==(graph(2,((0,1),)),(1,1,0)))
    f=from_blocks(leaves[1][0],((0,),(1,)),((1,1,0),)*2)
    r=from_blocks(leaves[2][0],((1,),(0,)),((1,1,0),)*2)
    check(f!=r and leaf_components(f)==leaf_components(r))
    forest=(identity(leaves[0]),f,r,identity(leaves[3]))
    result=subst(w,forest)
    check(ambient_blocks(result)==((0,),(1,),(3,),(4,),(2,),(5,)))
    # Recursively form full node cuts from global descendant intervals.
    def indices(shape):
        return (shape,) if isinstance(shape,int) else indices(shape[0])+indices(shape[1])
    def tree(shape):
        ids=indices(shape)
        vertices=tuple(v for v in range(6) if any(v in Bs[i] for i in ids))
        c=(induced(G,vertices),(path[ids[0]],path[ids[-1]+1],0))
        if isinstance(shape,int): return ('leaf',c)
        left=indices(shape[0]);boundary=left[-1]+1
        localword=tuple(0 if any(v in Bs[i] for i in left) else 1 for v in vertices)
        node=make(c[0],localword,((c[1][0],path[boundary],0),(path[boundary],c[1][1],0)),c[1])
        return ('node',node,tree(shape[0]),tree(shape[1]))
    def evaluate(t):
        return identity(t[1]) if t[0]=='leaf' else subst(t[1],(evaluate(t[2]),evaluate(t[3])))
    t1=tree(((0,1),(2,3)));t2=tree((0,(1,(2,3))))
    check(t1!=t2 and evaluate(t1)==evaluate(t2)==w)
    other=from_blocks(graph(6,E+((0,5),)),Bs,arrows(path))
    check(w!=other and w.matrix!=other.matrix and leaf_components(w)==leaf_components(other))
    empty=((),(1,1,0));unit=identity(empty);nullary=make((),(),(),(1,1,0))
    check(unit!=nullary and unit.arity==1 and nullary.arity==0)
    check(subst(unit,(nullary,))==nullary and subst(nullary,())==nullary)
    badpath=((0,1,0),(0,1,0),(1,1,0),(1,2,0))
    rejects={
      'nonidentity_loop_nullary':rejected(lambda:make((),(),(),(1,1,1))),
      'unequal_endpoint_nullary':rejected(lambda:make((),(),(),(0,1,0))),
      'nonempty_nullary':rejected(lambda:make(G,(0,)*6,(),(1,1,0))),
      'overlap':rejected(lambda:from_blocks(G,((0,1,2),(2,3,4,5)),((0,1,0),(1,2,0)))),
      'missing':rejected(lambda:from_blocks(G,((0,1,2),(3,4)),((0,1,0),(1,2,0)))),
      'noncomposable':rejected(lambda:from_blocks(G,Bs,badpath)),
      'wrong_grade':rejected(lambda:from_blocks(G,Bs,((0,1,1),)+arrows(path)[1:],(0,2,0))),
      'wrong_replacement_graph':rejected(lambda:subst(w,(identity(((),(0,1,0))),)+forest[1:])),
      'wrong_replacement_grade':rejected(lambda:subst(w,(identity(leaves[0]),make(f.matrix,f.word,((1,1,1),(1,1,0))),r,identity(leaves[3])))),
    }
    check(all(rejects.values()),'negative control')
    # Explicit invalid implementations, not success flags copied from tests.
    cache={c:v for c,v in zip(leaves,forest)}
    collapsed=subst(w,tuple(cache[c] for c in leaves))
    whole_erasure=lambda c:(c.word,c.arity,c.arrows)
    no_lift=tuple(b for child in forest for b in ambient_blocks(child))
    endpoint_only=lambda c:c.grade[0]==c.grade[1] and len(c.matrix)==0
    badnull=Cut((),(1,1,1),0,(),())
    endsonly=lambda p:p[0][0]==0 and p[-1][1]==2
    dropempty=lambda c:tuple(b for b in ambient_blocks(c) if b)
    mutants={
      'erase_whole':whole_erasure(w)==whole_erasure(other) and w!=other,
      'collapse_equal_components':collapsed!=result,
      'no_canonical_lift':no_lift!=ambient_blocks(result),
      'drop_arrow_values':endpoint_only(badnull) and not valid(badnull),
      'drop_internal_typing':endsonly(badpath) and not valid(Cut(G,(0,2,0),4,w.word,badpath)),
      'delete_empty_leaf':dropempty(unit)==dropempty(nullary) and unit!=nullary,
    }
    check(all(mutants.values()),'mutant survived')
    # Supplementary [2] x C2 composition identities/associativity and nullary iff.
    grade_cases=0
    for a in range(3):
      for b in range(a,3):
       for bit in range(2):
        check(valid(Cut((),(a,b,bit),0,(),()))==(a==b and bit==0));grade_cases+=1
    return {'repeated_nonempty_component':True,'ordered_refined_blocks':ambient_blocks(result),
            'groupings_distinct_full_evaluations_equal':True,'cross_edge_wholes_distinct_leaves_equal':True,
            'negative_controls':rejects,'mutants_killed':mutants,'all_empty_graph_grade_nullary_cases':grade_cases}

def basic_suite():
    count=Counter()
    for m in range(4):
      for G in all_graphs(m):
        count['graphs']+=1
        for selected in product((0,1),repeat=m):
          B=tuple(i for i,b in enumerate(selected) if b)
          for sub in product((0,1),repeat=len(B)):
            C=tuple(i for i,b in enumerate(sub) if b)
            ambient=tuple(B[i] for i in C)
            check(induced(induced(G,B),C)==induced(G,ambient))
            count['canonical_nested_restrictions']+=1
        for n in range(4):
          for lab in words(m,n):
            for chain in chains(n+1):
              w=make(G,lab,arrows(chain),(chain[0],chain[-1],0));count['cuts']+=1
              ids=tuple(identity(c) for c in leaf_components(w))
              check(subst(w,ids)==w);count['right_unit']+=1
              check(subst(identity((G,w.grade)),(w,))==w);count['left_unit']+=1
              for i,(H,grade) in enumerate(leaf_components(w)):
                for k in range(3):
                  for local in words(len(H),k):
                    for q in chains(k+1):
                      if (q[0],q[-1])!=grade[:2]:continue
                      v=make(H,local,arrows(q),grade)
                      forest=ids[:i]+(v,)+ids[i+1:]
                      result=subst(w,forest)
                      check(result.matrix==G and result.grade==w.grade)
                      check(leaf_components(result)==tuple(c for f in forest for c in leaf_components(f)))
                      count['single_occurrence_refinements']+=1
    return dict(count)

@lru_cache(None)
def shapes(depth):
    if depth==0:return (None,)
    children=shapes(depth-1)
    return ((),)+tuple((x,) for x in children)+tuple((x,y) for x in children for y in children)

def layout(shape, start=0):
    if shape is None:return (start,start+1,())
    cursor=start;cs=[]
    for child in shape:
        l=layout(child,cursor);cursor=l[1];cs.append(l)
    return (start,cursor,tuple(cs))

def template(G, lab, node):
    lo,hi,children=node
    vertices=tuple(v for v,x in enumerate(lab) if lo<=x<hi)
    local=tuple(next(i for i,c in enumerate(children) if c[0]<=lab[v]<c[1]) for v in vertices)
    return (induced(G,vertices),local,tuple((c[0],c[1]) for c in children),lo,hi)

def instantiate(data,chain):
    G,lab,bounds,lo,hi=data
    return make(G,lab,tuple((chain[a],chain[b],0) for a,b in bounds),(chain[lo],chain[hi],0))

def associativity_suite(full_product):
    counts=Counter();leaf_hist=Counter()
    domain=shapes(3);counts['shapes']=len(domain)
    for index,shape in enumerate(domain):
        root=layout(shape); L=root[1];leaf_hist[L]+=1
        interface_domain=chains(L+1)
        counts['interface_shape_chains']+=len(interface_domain)
        for m in range(4):
          for G in all_graphs(m):
            for lab in words(m,L):
              ts=template(G,lab,root)
              ms=tuple(template(G,lab,x) for x in root[2])
              bs=tuple(tuple(template(G,lab,y) for y in x[2]) for x in root[2])
              counts['graph_shape_label_assignments']+=1
              counts['product_domain_cardinality']+=len(interface_domain)
              todo=interface_domain if full_product else (interface_domain[counts['graph_shape_label_assignments']%len(interface_domain)],)
              for chain in todo:
                outer=instantiate(ts,chain);middle=tuple(instantiate(x,chain) for x in ms)
                bottom=tuple(tuple(instantiate(x,chain) for x in row) for row in bs)
                left=subst(subst(outer,middle),tuple(x for row in bottom for x in row))
                right=subst(outer,tuple(subst(x,row) for x,row in zip(middle,bottom)))
                expected=make(G,lab,arrows(chain),(chain[0],chain[-1],0))
                check(left==right==expected,'full typed associativity')
                counts['executed_full_typed_cases']+=1
        if index%20==0:print('Associativity progress',index+1,'/',len(domain),dict(counts),flush=True)
    check(sum(leaf_hist.values())==183)
    closed_count=sum(multiplicity*comb(L+3,2)*sum((1<<(m*(m-1)//2))*(L**m) for m in range(4)) for L,multiplicity in leaf_hist.items())
    check(counts['product_domain_cardinality']==closed_count)
    return {'counts':dict(counts),'leaf_count_histogram':dict(sorted(leaf_hist.items())),'independent_closed_count':closed_count}

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--full-product',action='store_true');args=parser.parse_args()
    started=time.time();result={'status':'RUNNING','independence':'No author-code imports or result reads; separately authored matrix/label implementation. Same-model agent review, not external human review.','full_product_requested':args.full_product,'python':sys.version}
    try:
      result['six_vertex']=six_vertex();print('Independent six-vertex/boundary/mutation controls PASS',flush=True)
      result['basic_suite']=basic_suite();print('Independent basic suite',result['basic_suite'],flush=True)
      result['associativity_suite']=associativity_suite(args.full_product)
      result['status']='PASS'
    except Exception as exc:
      result['status']='FAIL';result['error']=repr(exc);raise
    finally:
      result['duration_seconds']=time.time()-started
      result['source_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
      result['contract_sha256']=hashlib.sha256((ROOT/'research/CompletionContract.md').read_bytes()).hexdigest()
      result['target_sha256']=hashlib.sha256((ROOT/'research/workstream_C1/C1_Targets.md').read_bytes()).hexdigest()
      (HERE/'independent_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print('Independent final',json.dumps(result),flush=True)

if __name__=='__main__':main()
