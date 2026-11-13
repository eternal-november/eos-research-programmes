#!/usr/bin/env python3
"""Finite independent regression for B2, not an unrestricted quotient proof.

The checked target is the full-profile additive witness-statistic calculus.
It is a model of the actual associativity declarations, but its equality is NOT
used to define their congruence or asserted complete for that congruence.
"""
from __future__ import annotations
from dataclasses import dataclass
from itertools import product
import argparse, json
from pathlib import Path

Component = tuple[int, int]

@dataclass(frozen=True)
class Tree:
    output: Component
    kind: str = 'leaf'
    children: tuple['Tree', ...] = ()
    def __post_init__(self):
        a, c = self.output
        if self.kind == 'leaf':
            assert not self.children
        elif self.kind == 'binary':
            assert len(self.children) == 2
            x, y = self.children
            assert x.output[0] == a and x.output[1] == y.output[0] and y.output[1] == c
        elif self.kind in ('red', 'blue'):
            assert len(self.children) == 1 and self.children[0].output == self.output
        elif self.kind == 'zero':
            assert a == c and not self.children
        else:
            raise ValueError(self.kind)
    def leaves(self):
        return (self.output,) if self.kind == 'leaf' else tuple(c for t in self.children for c in t.leaves())
    def weights(self):
        own = tuple(int(self.kind == k) for k in ('binary', 'red', 'blue', 'zero'))
        return tuple(x + sum(t.weights()[j] for t in self.children) for j, x in enumerate(own))

def leaf(a,b): return Tree((a,b))
def join(t,u): return Tree((t.output[0],u.output[1]),'binary',(t,u))
def unary(k,t): return Tree(t.output,k,(t,))
def zero(a): return Tree((a,a),'zero')
def graft(t, forest):
    forest = tuple(forest)
    assert len(forest) == len(t.leaves())
    assert all(s.output == c for s,c in zip(forest,t.leaves()))
    it = iter(forest)
    def walk(u):
        return next(it) if u.kind == 'leaf' else Tree(u.output,u.kind,tuple(walk(v) for v in u.children))
    out = walk(t)
    assert next(it,None) is None
    return out

@dataclass(frozen=True)
class Operation:
    output: Component
    profile: tuple[Component,...]
    weights: tuple[int,int,int,int]
    def __post_init__(self):
        if self.profile:
            assert self.profile[0][0] == self.output[0]
            assert self.profile[-1][1] == self.output[1]
            assert all(x[1] == y[0] for x,y in zip(self.profile,self.profile[1:]))
        else:
            assert self.output[0] == self.output[1]
        assert all(w >= 0 for w in self.weights)

def evaluate(t): return Operation(t.output,t.leaves(),t.weights())
def identity(c): return Operation(c,(c,),(0,0,0,0))
def substitute(a, forest):
    forest=tuple(forest)
    assert tuple(b.output for b in forest) == a.profile
    return Operation(a.output,tuple(c for b in forest for c in b.profile),
        tuple(a.weights[j]+sum(b.weights[j] for b in forest) for j in range(4)))
def compose(forest, after):
    forest,after=tuple(forest),tuple(after)
    assert tuple(c for b in forest for c in b.profile) == tuple(b.output for b in after)
    offset=0; result=[]
    for b in forest:
        n=len(b.profile)
        result.append(substitute(b,after[offset:offset+n])); offset+=n
    assert offset == len(after)
    return tuple(result)

def check():
    counts={'associativity_instances':0,'loop_parallel_pairs':0,'two_layer_compositions':0,
            'three_layer_compositions':0,'nullary_second_layers':0}
    for a,b,c,d in product(range(3), repeat=4):
        L=join(join(leaf(a,b),leaf(b,c)),leaf(c,d))
        R=join(leaf(a,b),join(leaf(b,c),leaf(c,d)))
        assert L != R and evaluate(L)==evaluate(R)
        counts['associativity_instances']+=1
    for a in range(3):
        x=leaf(a,a); mu=join(x,x)
        L,R=graft(mu,(mu,x)),graft(mu,(x,mu))
        assert L!=R
        f,g=(evaluate(mu),evaluate(x)),(evaluate(x),evaluate(mu))
        assert f!=g and substitute(evaluate(mu),f)==substitute(evaluate(mu),g)
        assert graft(mu,(x,mu)) != L
        counts['loop_parallel_pairs']+=1
        choices=(x,unary('red',x),unary('blue',x),mu,zero(a))
        for hs in product(choices, repeat=3):
            h=tuple(map(evaluate,hs))
            for base in (f,g):
                composed=compose(base,h)
                assert substitute(substitute(evaluate(mu),base),h)==substitute(evaluate(mu),composed)
                assert compose(base,tuple(identity(c) for c in evaluate(L).profile))==base
                counts['two_layer_compositions']+=1
            if any(t.kind=='zero' for t in hs): counts['nullary_second_layers']+=1
            # Distinction tested where unary substitutions preserve segmentation;
            # no blanket cancellation claim is made for arbitrary nullary tuples.
            if all(len(t.leaves())==1 for t in hs): assert compose(f,h)!=compose(g,h)
            outprofile=tuple(c for t in hs for c in t.leaves())
            k=tuple(evaluate(unary('red',leaf(*c))) for c in outprofile)
            assert compose(compose(f,h),k)==compose(f,compose(h,k))
            counts['three_layer_compositions']+=1
    x=leaf(1,1); mu=join(x,x)
    context=lambda t:join(leaf(0,1),join(t,leaf(1,2)))
    source=context(mu); L=context(graft(mu,(mu,x))); R=context(graft(mu,(x,mu)))
    assert source.leaves()==((0,1),(1,1),(1,1),(1,2))
    assert len(source.leaves())==4 and len(L.leaves())==5
    assert L!=R and evaluate(L)==evaluate(R)
    f=tuple(map(evaluate,(leaf(0,1),mu,x,leaf(1,2))))
    g=tuple(map(evaluate,(leaf(0,1),x,mu,leaf(1,2))))
    assert f!=g and substitute(evaluate(source),f)==substitute(evaluate(source),g)
    red,blue=unary('red',x),unary('blue',x)
    assert evaluate(red)!=evaluate(blue)
    # Negative control retains the COMPLETE typed profile but discards witnesses.
    discard=lambda t:(t.output,t.leaves())
    assert discard(red)==discard(blue)
    assert discard(L)==discard(R)
    # Deliberate invalid tuple: same total length cannot repair wrong slot outputs.
    try:
        substitute(evaluate(source),(identity((0,1)),identity((0,1)),identity((1,1)),identity((1,2))))
    except AssertionError: pass
    else: raise AssertionError('mistyped occurrence family accepted')
    return {'status':'PASS','evidence_class':'C','domain':'interfaces {0,1,2}; 81 associativity instances; five loop replacements',
            'caveat':'Witness-statistic model checks, not an exact algorithm for the A3 quotient.',
            'counts':counts,'mixed_profile':[list(c) for c in source.leaves()],
            'negative_controls':['full-profile witness erasure equates red and blue','wrong component at occurrence rejected']}

if __name__=='__main__':
    p=argparse.ArgumentParser(); p.add_argument('--output'); args=p.parse_args()
    result=check(); text=json.dumps(result,indent=2)+'\n'; print(text,end='')
    if args.output: Path(args.output).write_text(text)
