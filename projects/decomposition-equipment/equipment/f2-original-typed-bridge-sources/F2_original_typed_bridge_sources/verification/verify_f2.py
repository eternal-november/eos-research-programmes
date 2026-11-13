#!/usr/bin/env python3
"""Exact, factorized original graph-cut F2 tests. Standard library only; assertions are mandatory."""
if not __debug__:
    raise RuntimeError("Assertions are required; do not use -O or PYTHONOPTIMIZE.")
import itertools as I, json, time, hashlib
from pathlib import Path
from collections import Counter, defaultdict
from functools import lru_cache
C=Counter()
@lru_cache(None)
def maps(n,m): # [m] -> [n]
    return tuple(I.combinations_with_replacement(range(n+1),m+1))
def active(a,n): return a[0]==0 and a[-1]==n
@lru_cache(None)
def parts(v,n): return tuple(I.product(range(1,n+1),repeat=v))
@lru_cache(None)
def graphs(v):
    pairs=tuple(I.combinations(range(v),2))
    return tuple(frozenset(p for i,p in enumerate(pairs) if mask>>i&1) for mask in range(1<<len(pairs)))
def transform(b,a):
    return next((j for j in range(1,len(a)) if a[j-1]<b<=a[j]),None)
def geom(p,e,a):
    labels=[transform(b,a) for b in p]
    selected=[i for i,b in enumerate(labels) if b is not None]
    ren={v:i for i,v in enumerate(selected)}
    return (tuple(labels[i] for i in selected),frozenset((ren[u],ren[v]) for u,v in e if u in ren and v in ren))
def geom_reference(p,e,a):
    # Independent block-set definition; does not call transform or geom.
    blocks=[set(i for i,b in enumerate(p) if a[j-1]<b<=a[j]) for j in range(1,len(a))]
    vertices=sorted(set().union(*blocks)) if blocks else []
    labels=tuple(next(j+1 for j,B in enumerate(blocks) if v in B) for v in vertices)
    edges=frozenset((i,j) for i in range(len(vertices)) for j in range(i+1,len(vertices)) if (vertices[i],vertices[j]) in e)
    return labels,edges
@lru_cache(None)
def paths(n): return tuple(I.combinations_with_replacement(range(3),n+1))
def path_action(h,a): return tuple(h[i] for i in a)
def compose(a,b): return tuple(a[i] for i in b)
@lru_cache(None)
def trees(i,j):
    if j==i+1:return (None,)
    return tuple((k,L,R) for k in range(i+1,j) for L in trees(i,k) for R in trees(k,j))
def restrict_graph(v,e,S):
    S=tuple(sorted(S)); rank={x:i for i,x in enumerate(S)}
    return len(S),frozenset((rank[x],rank[y]) for x,y in e if x in rank and y in rank)
def targets(v,e,t,i,j):
    """Independently enumerate compatible triangle records with fixed root edge.
    Only binary partitions are enumerated. No n-block record is supplied/split.
    Tree tuple records retain root graph and its binary partition at every node.
    """
    if t is None:
        yield None; return
    k,L,R=t
    for q in I.product((1,2),repeat=v):
        A=tuple(x for x in range(v) if q[x]==1); B=tuple(x for x in range(v) if q[x]==2)
        av,ae=restrict_graph(v,e,A); bv,be=restrict_graph(v,e,B)
        for left in targets(av,ae,L,i,k):
            for right in targets(bv,be,R,k,j):yield (q,e,left,right)
def reconstruct(v,e,d,t,i,j):
    if t is None:
        assert d is None
        return (1,)*v,e
    k,L,R=t; q,root,ld,rd=d
    assert root==e
    A=tuple(x for x in range(v) if q[x]==1); B=tuple(x for x in range(v) if q[x]==2)
    lp,_=reconstruct(*restrict_graph(v,e,A),ld,L,i,k)
    rp,_=reconstruct(*restrict_graph(v,e,B),rd,R,k,j)
    out=[None]*v
    for x,b in zip(A,lp):out[x]=b
    for x,b in zip(B,rp):out[x]=b+k-i
    return tuple(out),root

def comparison(p,e,t,i,j):
    if t is None:return None
    k,L,R=t
    q=tuple(1 if b<=k-i else 2 for b in p)
    lp,le=geom(p,e,tuple(range(k-i+1)))
    rp,re=geom(p,e,tuple(range(k-i,j-i+1)))
    return q,e,comparison(lp,le,L,i,k),comparison(rp,re,R,k,j)

def category_targets(t,i,j,a,b):
    if t is None:
        yield None;return
    k,L,R=t
    # Actual [2] arrows are pairs (a,c),(c,b), not untyped placeholders.
    for c in range(a,b+1):
        for left in category_targets(L,i,k,a,c):
            for right in category_targets(R,k,j,c,b):yield ((a,c,b),left,right)
def category_reconstruct(d,t,a,b):
    if t is None:return (a,b)
    k,L,R=t; (x,c,y),ld,rd=d
    assert (x,y)==(a,b)
    return category_reconstruct(ld,L,a,c)[:-1]+category_reconstruct(rd,R,c,b)
def category_compare(h,t,i,j):
    if t is None:return None
    k,L,R=t
    return (h[0],h[k-i],h[-1]),category_compare(h[:k-i+1],L,i,k),category_compare(h[k-i:],R,k,j)

def check():
    # Compositional geometry: full independent actions plus exhaustive atom laws.
    # Rank-preserving induced edges are functorial iff these atom selections are.
    for n in range(5):
      for m in range(5):
       for a in maps(n,m):
        for l in range(5):
         for b in maps(m,l):
          ab=compose(a,b)
          for color in range(1,n+1):
            first=transform(color,a)
            assert (None if first is None else transform(first,b))==transform(color,ab)
            C['geometry_composition_vertex_atoms']+=1
          for h in paths(n):
            assert path_action(path_action(h,a),b)==path_action(h,ab)
            C['category_composition_checks']+=1
          C['monotone_composable_map_pairs']+=1
    for n in range(5):
     for h in paths(n):
      assert path_action(h,tuple(range(n+1)))==h
      C['category_records']+=1
     for v in range(5):
      for p in parts(v,n):
       for e in graphs(v):
        C['graph_records']+=1; C[f'graph_records_degree_{n}']+=1
        assert geom(p,e,tuple(range(n+1)))==(p,e)
        for m in range(5):
         for a in maps(n,m):
          assert geom(p,e,a)==geom_reference(p,e,a)
          C['all_graph_monotone_actions']+=1
    # Targets enumerate all binary triangle data, independently of source records.
    for n in range(2,5):
     assert len(trees(0,n))=={2:1,3:2,4:5}[n]
     for ti,t in enumerate(trees(0,n)):
      C[f'triangulations_degree_{n}']+=1
      for v in range(5):
       for e in graphs(v):
        seen=set()
        for d in targets(v,e,t,0,n):
          p,f=reconstruct(v,e,d,t,0,n)
          assert f==e and p not in seen
          seen.add(p)
          assert comparison(p,e,t,0,n)==d
          C['triangle_target_inverse_checks']+=1
          C[f'triangle_targets_degree_{n}_triangulation_{ti}']+=1
        assert seen==set(parts(v,n))
        for p in parts(v,n):
          assert reconstruct(v,e,comparison(p,e,t,0,n),t,0,n)==(p,e)
          C['triangle_source_inverse_checks']+=1
      for a in range(3):
       for b in range(a,3):
        seen=set()
        for d in category_targets(t,0,n,a,b):
          h=category_reconstruct(d,t,a,b)
          assert h not in seen; seen.add(h)
          assert category_compare(h,t,0,n)==d
          C['category_triangle_inverse_checks']+=1
        assert seen=={h for h in paths(n) if (h[0],h[-1])==(a,b)}
    # Pentagon: transition maps defined on independently generated target data.
    ts=trees(0,4)
    # Flips adjacency: share one of two internal diagonals.
    def diagonals(t,i,j):
        if t is None:return set()
        k,L,R=t
        return ({(i,k)} if k-i>1 else set())|({(k,j)} if j-k>1 else set())|diagonals(L,i,k)|diagonals(R,k,j)
    adj={i:[j for j in range(5) if i!=j and len(diagonals(ts[i],0,4)&diagonals(ts[j],0,4))==1] for i in range(5)}
    assert all(len(a)==2 for a in adj.values())
    cycle=[0,adj[0][0]]
    while len(cycle)<5:cycle.append(next(j for j in adj[cycle[-1]] if j!=cycle[-2]))
    assert cycle[0] in adj[cycle[-1]] and len(set(cycle))==5
    for v in range(5):
     for e in graphs(v):
      for d in targets(v,e,ts[0],0,4):
       out=d
       for a,b in zip(cycle,cycle[1:]+[0]):
        p,f=reconstruct(v,e,out,ts[a],0,4)
        out=comparison(p,f,ts[b],0,4)
       assert out==d
       C['pentagon_target_cycles']+=1
    # Unit pullbacks: enumerate target records with selected edge empty/identity,
    # then independently delete boundary; compare bijections to source degeneracy.
    for n in range(4):
     for i in range(n+1):
      sigma=tuple(range(i+1))+(i,)+tuple(range(i+1,n+1))
      for v in range(5):
       for e in graphs(v):
        target={p for p in parts(v,n+1) if i+1 not in p}
        source=set(parts(v,n))
        images={geom(p,e,sigma)[0] for p in source}
        assert images==target and len(images)==len(source)
        for p in target:
          q=tuple(b if b<i+1 else b-1 for b in p)
          assert q in source and geom(q,e,sigma)==(p,e)
          C['unit_graph_pullback_objects']+=1
      target={h for h in paths(n+1) if h[i]==h[i+1]}
      images={path_action(h,sigma) for h in paths(n)}
      assert images==target and len(images)==len(paths(n))
      for h in target:
        assert path_action(h[:i]+h[i+1:],sigma)==h
        C['unit_category_pullback_objects']+=1
    p=(1,2); e0=frozenset();e1=frozenset({(0,1)})
    assert (p,e0)!=(p,e1)
    assert all(geom(p,e0,(i,i+1))==geom(p,e1,(i,i+1)) for i in range(2))
    assert geom(p,e1,(1,2))==((1,),frozenset())
    C['ordinary_segal_noninjective_pair']=1; C['outer_face_loses_cross_edge']=1
    # Mutation: root cross edges cannot be reconstructed from its two induced pieces.
    d=next(d for d in targets(2,e1,trees(0,2)[0],0,2) if d[0]==p)
    assert reconstruct(2,e1,d,trees(0,2)[0],0,2)!=(p,e0)
    C['mutation_forget_root_edges_detected']=1
    # Malformed compatible-target control: shared diagonal graph mismatch.
    t=next(t for t in trees(0,3) if t[0]==2)
    good=comparison((1,2),e1,t,0,3)
    q,root,left,right=good
    lq,le,ll,lr=left
    bad=(q,root,(lq,e0,ll,lr),right)
    rejected=False
    try: reconstruct(2,e1,bad,t,0,3)
    except AssertionError: rejected=True
    assert rejected
    C['mutation_mismatched_shared_diagonal_detected']=1
    # Empty graph alone is NOT the categorical unit: nonidentity arrows excluded.
    assert (0,1) not in {path_action(h,(0,0)) for h in paths(0)}
    C['empty_graph_nonidentity_not_unit']=1
    assert (0,1) in paths(1) and (1,2) in paths(1) and path_action((0,1,2),(0,2))==(0,2)
    C['actual_nonidentity_arrow_composition']=1
    # Exact C1 section 8 fixture and its original two-representation checks.
    import c1_reference
    fixture=c1_reference.six_vertex()
    p=(1,2,3,2,3,4); e=frozenset({(0,1),(1,2),(1,3),(2,4),(3,4),(4,5)})
    h=(0,1,1,1,2)
    for f in (e,e|{(0,5)}):
      for t in trees(0,4):
        assert reconstruct(6,f,comparison(p,f,t,0,4),t,0,4)==(p,f)
        assert category_reconstruct(category_compare(h,t,0,4),t,0,2)==h
        C['six_vertex_triangulations']=C['six_vertex_triangulations']+1
      for m in range(5):
       for a in maps(4,m):
        assert geom(p,f,a)==geom_reference(p,f,a)
        for l in range(5):
         for b in maps(m,l):
          assert geom(*geom(p,f,a),b)==geom(p,f,compose(a,b))
          C['six_vertex_full_geometry_compositions']+=1
    return fixture
if __name__=='__main__':
    start=time.time();fixture=check()
    result={'status':'PASS','scope':'bounded executable evidence, not all-degree theorem or independent acceptance','bounds':{'ordered_simple_graph_vertices':list(range(5)),'simplicial_degrees':list(range(5)),'all_monotone_maps_between_bounded_degrees':True,'all_composable_pairs_with_all_three_degrees_bounded':True,'category':'[2]: objects 0,1,2; six arrows (i,j), i<=j; (j,k) composed with (i,j)=(i,k)','ordered_partitions':'all functions vertices -> {1,...,n}, including empty blocks and noncontiguous blocks','unit_squares':'all n->n+1 with n+1<=4, every position','triangulations':'1 triangle, both quadrilateral, all five pentagon','six_vertex':'exact original C1 section 8 plus G+05'},'counts':dict(sorted(C.items())),'six_vertex_fixture':fixture,'factorization':'Independent graph and category coordinates; composition atom reduction plus full independently implemented action checks. Triangle targets enumerated independently by compatible binary records, not solely split/rejoin of source.','source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'c1_reference_sha256':hashlib.sha256(Path(__file__).with_name('c1_reference.py').read_bytes()).hexdigest()}
    Path(__file__).with_name('results.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True));print('Elapsed seconds (noncertificate):',round(time.time()-start,3))
