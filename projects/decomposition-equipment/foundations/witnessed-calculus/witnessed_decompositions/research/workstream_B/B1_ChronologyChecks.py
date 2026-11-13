#!/usr/bin/env python3
"""Finite C regressions, never substituted for B1's unrestricted P/L proofs.

Two independent chronology enumerators: legal current-leaf execution versus
permutation filtering by the final forest's ancestor order. No third-party deps.
"""
from __future__ import annotations
from dataclasses import dataclass
from functools import lru_cache
from itertools import product, permutations
from collections import deque
import json

Component = tuple[int, int]
Address = tuple[int, ...]

@dataclass(frozen=True)
class Gen:
    name: str
    output: Component
    inputs: tuple[Component, ...]
    def __post_init__(self):
        if not self.inputs:
            assert self.output[0] == self.output[1]
        else:
            assert self.inputs[0][0] == self.output[0]
            assert self.inputs[-1][1] == self.output[1]
            assert all(a[1] == b[0] for a,b in zip(self.inputs,self.inputs[1:]))

@dataclass(frozen=True)
class Tree:
    output: Component
    gen: Gen | None = None
    children: tuple[Tree, ...] = ()
    def __post_init__(self):
        if self.gen is None:
            assert not self.children
        else:
            assert self.output == self.gen.output
            assert tuple(t.output for t in self.children) == self.gen.inputs

def leaf(c): return Tree(c)
def node(g, *children): return Tree(g.output, g, tuple(children))
def corolla(g): return node(g, *(leaf(c) for c in g.inputs))

def data(t, root=()):
    """Independent edge/vertex/leaf address representation."""
    edges = {root:t.output}
    vertices = {} if t.gen is None else {root:t.gen}
    leaves = [root] if t.gen is None else []
    for i,ch in enumerate(t.children):
        e,v,l = data(ch,root+(i,))
        edges.update(e); vertices.update(v); leaves.extend(l)
    return edges,vertices,leaves

def subtree(t,a):
    for i in a:
        assert t.gen is not None and i < len(t.children)
        t=t.children[i]
    return t

def graft(t,forest,root=()):
    if t.gen is None:
        x=forest[root]
        assert x.output == t.output
        return x
    return node(t.gen,*(graft(ch,forest,root+(i,)) for i,ch in enumerate(t.children)))

def prefix(t,u):
    if t.output != u.output: return False
    vt=data(t)[1]; vu=data(u)[1]
    return all(a in vu and vu[a] == g for a,g in vt.items())

def recover(t,u):
    """Structural reconstruction, separate from the prefix predicate."""
    if t.output != u.output: return None
    if t.gen is None: return {():u}
    if t.gen != u.gen: return None
    out={}
    for i,(tc,uc) in enumerate(zip(t.children,u.children)):
        f=recover(tc,uc)
        if f is None: return None
        out.update({(i,)+a:x for a,x in f.items()})
    return out

def atomic(t,a,g):
    edges,vertices,leaves=data(t)
    if a not in leaves or edges[a] != g.output:
        raise ValueError('not a typed current leaf')
    forest={b:leaf(edges[b]) for b in leaves}
    forest[a]=corolla(g)
    return graft(t,forest)

def proper_prefix(a,b): return len(a)<len(b) and b[:len(a)]==a

def event_history_by_execution(t,u):
    """Check legality in actual changing trees; never reads the ancestor order."""
    final=data(u)[1]
    out=[]
    def go(cur,hist):
        if cur == u:
            out.append(tuple(hist)); return
        edges,vs,ls=data(cur)
        for a in ls:
            if a in final:
                nxt=atomic(cur,a,final[a])
                go(nxt,hist+[a])
    go(t,[])
    return set(out)

def linear_extensions(t,u):
    """Brute permutation filter, never executes or checks current leaf legality."""
    old=data(t)[1]; new=data(u)[1]
    events=tuple(a for a in new if a not in old)
    relations=[(a,b) for a in events for b in events if proper_prefix(a,b)]
    out=set()
    for order in permutations(events):
        rank={a:i for i,a in enumerate(order)}
        if all(rank[a]<rank[b] for a,b in relations): out.add(order)
    return out

def interchange_component(histories):
    if not histories: return set()
    seen={next(iter(histories))}; q=deque(seen)
    while q:
        h=q.popleft()
        for i in range(len(h)-1):
            a,b=h[i:i+2]
            if not proper_prefix(a,b) and not proper_prefix(b,a):
                h2=h[:i]+(b,a)+h[i+2:]
                assert h2 in histories
                if h2 not in seen: seen.add(h2);q.append(h2)
    return seen

X=(1,1)
G=Gen('binary',X,(X,X)); H=Gen('other-binary',X,(X,X))
U=Gen('unary',X,(X,)); Z=Gen('nullary',X,())
SIG=(G,H,U,Z)

@lru_cache(None)
def exact_trees(n):
    if n==0: return (leaf(X),)
    out=[]
    for g in SIG:
        if len(g.inputs)==0:
            if n==1:out.append(corolla(g))
        elif len(g.inputs)==1:
            out.extend(node(g,t) for t in exact_trees(n-1))
        else:
            for a in range(n):
                out.extend(node(g,t,s) for t in exact_trees(a) for s in exact_trees(n-1-a))
    return tuple(out)

def main():
    trees=tuple(t for n in range(4) for t in exact_trees(n))
    pair_checks=0
    for t,u in product(trees,repeat=2):
        f=recover(t,u)
        assert (f is not None)==prefix(t,u)
        if f is not None:
            assert graft(t,f)==u
            assert f == {a:subtree(u,a) for a in data(t)[2]}
        if prefix(t,u) and prefix(u,t): assert t==u
        pair_checks+=1
    forest_checks=0; history_cases=0; history_total=0; rank_checks=0
    small=exact_trees(0)+exact_trees(1)
    for t in exact_trees(0)+exact_trees(1)+exact_trees(2):
        leaves=data(t)[2]
        seen={}
        for entries in product(small,repeat=len(leaves)):
            f=dict(zip(leaves,entries)); u=graft(t,f)
            assert u not in seen or seen[u]==f
            seen[u]=f
            assert recover(t,u)==f
            actual=data(u)[2]
            expected=[a+b for a in leaves for b in data(f[a])[2]]
            assert actual==expected
            offset=0
            for a in leaves:
                for j,b in enumerate(data(f[a])[2]):
                    assert actual.index(a+b)==offset+j;rank_checks+=1
                offset+=len(data(f[a])[2])
            assert len(actual)==offset
            if sum(len(data(e)[1]) for e in entries)<=3:
                exe=event_history_by_execution(t,u); linear=linear_extensions(t,u)
                assert exe==linear and len(exe)>0
                assert interchange_component(exe)==exe
                history_cases+=1;history_total+=len(exe)
            forest_checks+=1
    # Mixed 0→1→1→1→2 context, with repeated identical loop components.
    p=(0,1);q=(1,2);w=(0,2)
    context=Gen('mixed-context',w,(p,X,X,q))
    t=corolla(context)
    # Six added events, including unary dependence and a nullary deletion.
    f={(0,):leaf(p),(1,):node(G,node(U,leaf(X)),corolla(Z)),
       (2,):node(H,corolla(U),corolla(U)),(3,):leaf(q)}
    u=graft(t,f)
    ex=event_history_by_execution(t,u);le=linear_extensions(t,u)
    assert ex==le and interchange_component(ex)==ex
    assert len(data(t)[2])==4 and len(data(u)[2])==5
    # Independent sibling event orders exist; a child cannot precede its parent.
    assert any(h.index((1,))<h.index((2,)) for h in ex)
    assert any(h.index((2,))<h.index((1,)) for h in ex)
    try:atomic(t,(1,0),U)
    except ValueError:pass
    else:raise AssertionError('dependent child incorrectly allowed before parent')
    # Existing vertex cannot be changed, even by an equal-arity compatible witness.
    old=corolla(G); replacement=corolla(H)
    assert not prefix(old,replacement) and recover(old,replacement) is None
    try:atomic(old,(),H)
    except ValueError:pass
    else:raise AssertionError('internal vertex incorrectly treated as leaf')
    # Nullary event removes exactly one leaf; later ordinal shifts left.
    n=atomic(t,(1,),Z)
    assert data(n)[2]==[(0,),(2,),(3,)]
    assert data(n)[2].index((2,))==1
    # Three-level core address correspondence and typed composition, all mixed.
    uf=data(u)[2]; ue=data(u)[0]
    second={a:(corolla(U) if ue[a]==X else leaf(ue[a])) for a in uf}
    v=graft(u,second)
    composed={a:graft(f[a],{b:second[a+b] for b in data(f[a])[2]}) for a in data(t)[2]}
    assert graft(t,composed)==v
    triples=[(a,b,d) for a in data(t)[2] for b in data(f[a])[2]
             for d in data(second[a+b])[2]]
    assert [(a+b)+d for a,b,d in triples]==[a+(b+d) for a,b,d in triples]==data(v)[2]
    for a,b,d in triples:
        assert data(v)[0][a+b+d]==data(second[a+b])[0][d]
    # Discriminating mutation controls: identifying original leaves by equal label
    # would equate these unequal replacement trees, and must fail.
    assert f[(1,)].output==f[(2,)].output and f[(1,)]!=f[(2,)]
    assert not prefix(corolla(U),corolla(Z))
    report={
      'status':'PASS','evidence_class':'C only; unrestricted proof is B1_PrefixChronology.md',
      'finite_domain':{'loop_signature':['binary','other-binary','unary','nullary'],
                       'all_trees_max_vertices':3,'all_trees_count':len(trees),
                       'source_max_vertices':2,'replacement_max_vertices':1},
      'prefix_reconstruction_antisymmetry_pairs':pair_checks,
      'forest_recovery_injectivity_checks':forest_checks,
      'moving_frontier_rank_checks':rank_checks,
      'all_history_interchange_cases':history_cases,'enumerated_histories':history_total,
      'mixed_context':{'interfaces':[0,1,2],'source_leaves':4,'target_leaves':5,
                       'events':6,'linear_extensions':len(ex)},
      'negative_controls':['dependent event reversed','existing binary witness relabelled',
                           'nullary frontier-rank omission','equal-label occurrence collapse'],
      'three_layer_typed_occurrence_composition':'PASS'}
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
