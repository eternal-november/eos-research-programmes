#!/usr/bin/env python3
"""Finite regression fixtures for O3; these do not replace the general proofs."""
from fractions import Fraction as F
from itertools import product
from collections import defaultdict, Counter
from dataclasses import dataclass
import json


def leaf(x): return ('leaf', x)
def node(label, *children): return ('node', label, tuple(children))
def leaves(t):
    if t[0] == 'leaf': return [t[1]]
    return [x for c in t[2] for x in leaves(c)]
def graft(t, ts):
    it = iter(ts)
    def go(s):
        if s[0] == 'leaf': return next(it)
        return node(s[1], *(go(c) for c in s[2]))
    out = go(t)
    try: next(it)
    except StopIteration: return out
    raise AssertionError('extra leaf replacement')
def event_bag(t):
    if t[0] == 'leaf': return Counter()
    out=Counter({t[1]:1})
    for c in t[2]: out.update(event_bag(c))
    return out

def add(*cs): return tuple(map(sum,zip(*cs))) if cs else (0,0)
@dataclass(frozen=True)
class H:
    weight: F
    cost: tuple
    tree: tuple
    chronology: tuple

def ret(x): return [H(F(1),(0,0),leaf(x),())]
def bind(hs, k):
    out=[]
    for h in hs:
        choices=[k(x) for x in leaves(h.tree)]
        for ks in product(*choices):
            w=h.weight
            for z in ks:w*=z.weight
            out.append(H(w, add(h.cost,*(z.cost for z in ks)),
                         graft(h.tree,[z.tree for z in ks]),
                         h.chronology+sum((z.chronology for z in ks),())))
    return out

def law(hs, obs=lambda h:(h.cost,h.tree)):
    d=defaultdict(F)
    for h in hs:d[obs(h)]+=h.weight
    return {k:v for k,v in d.items() if v}

def normalized(hs): assert sum((h.weight for h in hs),F())==1

def fixture():
    acquire=[H(F(1,3),(1,0),node('acquire_L',leaf('L')),('acquire_L',)),
             H(F(2,3),(1,0),node('acquire_H',leaf('H1'),leaf('H2')),('acquire_H',))]
    probs={'L':F(3,4),'H1':F(1,2),'H2':F(2,3)}
    def read(x):
        c=(1,0) if x=='L' else (0,1)
        return [H(1-probs[x],c,node('read_'+x,leaf(0)),('read_'+x,)),
                H(probs[x],c,node('read_'+x,leaf(1)),('read_'+x,))]
    hs=bind(acquire,read); normalized(hs)
    assert len(hs)==6
    weights={tuple(leaves(h.tree)):h.weight for h in hs}
    assert weights=={(0,):F(1,12),(1,):F(1,4),(0,0):F(1,9),(0,1):F(2,9),(1,0):F(1,9),(1,1):F(2,9)}
    alarm=sum((h.weight for h in hs if any(leaves(h.tree))),F())
    assert alarm==F(29,36)
    assert all(h.cost[0]<=2 and h.cost[1]<=2 for h in hs)
    tight=sum((h.weight for h in hs if h.cost[0]<=2 and h.cost[1]<=1),F())
    assert tight==F(1,3)
    # Actual token discipline: each output branch is a disjoint subset.
    pool={'alpha','beta','gamma'}
    partitions=[({'alpha'},),({'beta'},{'gamma'})]
    for parts in partitions:
        assert set().union(*parts)<=pool
        assert sum(map(len,parts))==len(set().union(*parts))
    return {'raw_paths':len(hs),'alarm_probability':str(alarm),'tight_budget_probability':str(tight)}

def associativity():
    cases=0; paths=0
    for n in range(5):
        p=[H(F(1),(2,1),node('start'+str(n),*(leaf(i%2) for i in range(n))),('start',))]
        for qprob,rprob in product([F(0),F(1,3),F(1)],[F(0),F(1,2),F(1)]):
            def q(x):return [H(qprob,(x+1,0),node('q'+str(x),leaf(x)),('q'+str(x),)),
                             H(1-qprob,(0,x+1),node('qpair'+str(x),leaf(1-x),leaf(x)),('qpair'+str(x),))]
            def r(x):return [H(rprob,(1,x),node('r'+str(x),leaf(x)),('r'+str(x),)),
                             H(1-rprob,(x,1),node('stop'+str(x)),('stop'+str(x),))]
            left=bind(bind(p,q),r); right=bind(p,lambda x:bind(q(x),r))
            normalized(left); normalized(right)
            assert len(left)==len(right)
            # Raw comparison retains multiplicity and zero-weight histories.
            assert Counter((h.weight,h.cost,h.tree) for h in left)==Counter((h.weight,h.cost,h.tree) for h in right)
            assert law(left)==law(right)
            # Cartesian arity shadow and optional commutative event bag.
            assert law(left,lambda h:(h.cost,tuple(leaves(h.tree))))==law(right,lambda h:(h.cost,tuple(leaves(h.tree))))
            assert law(left,lambda h:(h.cost,tuple(sorted(event_bag(h.tree).items())),tuple(leaves(h.tree))))==law(right,lambda h:(h.cost,tuple(sorted(event_bag(h.tree).items())),tuple(leaves(h.tree))))
            assert law(bind(p,ret))==law(p)
            cases+=1; paths+=len(left)
    return {'parameter_cases':cases,'raw_paths_per_bracketing':paths,'raw_multiset_including_zero_weights':'equal'}

def chronology():
    p=[H(F(1),(0,0),node('split',leaf(1),leaf(2)),('split',))]
    def q(i):return [H(F(1),(0,0),node('q'+str(i),leaf(i)),('q'+str(i),))]
    def r(i):return [H(F(1),(0,0),node('r'+str(i),leaf(i)),('r'+str(i),))]
    a=bind(bind(p,q),r)[0];b=bind(p,lambda i:bind(q(i),r))[0]
    assert a.tree==b.tree
    assert a.chronology==('split','q1','q2','r1','r2')
    assert b.chronology==('split','q1','r1','q2','r2')
    assert a.chronology!=b.chronology
    return {'left':a.chronology,'right':b.chronology,'causal_tree_equal':True}

def zero_path():
    a=[H(F(1),(1,0),node('e_1',leaf('ok')),('e_1',))]
    b=a+[H(F(0),(100,0),node('e_1',leaf('ok')),('e_1',))]
    assert law(a)==law(b)
    assert all(h.cost[0]<=1 for h in a)
    assert not all(h.cost[0]<=1 for h in b)
    assert all(h.cost[0]<=100 for h in b)
    # Native inclusion allowed: target zero witness has empty source fibre.
    return {'joint_law_equal':True,'source_all_path_budget_1':True,'target_all_path_budget_1':False,'both_all_path_budget_100':True}

def native_coupling():
    ps=[F(1,4),F(1,4),F(1,2),F(0)]
    cs=[4,2,7,9]; r=[0,0,1,1]; qs=[F(1,2),F(1,2)];ds=[2,6]
    for y in range(2):
        assert sum((ps[x] for x in range(4) if r[x]==y),F())==qs[y]
        assert min(cs[x] for x in range(4) if r[x]==y)>=ds[y]
    assert all(cs[x]>=ds[r[x]] for x in range(4))
    bounds=0
    for b in range(12):
        src=sum((p for p,c in zip(ps,cs) if c<=b),F())
        tgt=sum((p for p,c in zip(qs,ds) if c<=b),F())
        assert tgt>=src;bounds+=1
    srcE=sum((p*c for p,c in zip(ps,cs)),F())
    tgtE=sum((p*c for p,c in zip(qs,ds)),F())
    assert (srcE,tgtE)==(F(5),F(4))
    assert set(r)=={0,1}
    assert max(ds)<=max(cs)
    return {'tested_bounds':bounds,'source_expected_cost':str(srcE),'target_expected_cost':str(tgtE),'raw_surjective':True}

def batch(hfamilies):
    out=[]
    for hs in product(*hfamilies):
        w=F(1)
        for h in hs:w*=h.weight
        out.append(H(w, add(*(h.cost for h in hs)),
                     node('Fork_'+str(len(hfamilies)),*(h.tree for h in hs)),
                     sum((h.chronology for h in hs),())))
    return out

def batch_fixtures():
    empty=batch([])
    assert empty==[H(F(1),(0,0),node('Fork_0'),())]
    assert leaves(empty[0].tree)==[]
    a=[H(F(1,3),(1,0),node('a',leaf(0)),('a',)),
       H(F(2,3),(2,0),node('a',leaf(1)),('a',))]
    b=[H(F(1,2),(0,1),node('b',leaf(2)),('b',)),
       H(F(1,2),(0,2),node('b',leaf(3)),('b',))]
    hs=batch([a,b]);normalized(hs)
    assert len(hs)==4
    assert {tuple(leaves(h.tree)) for h in hs}=={(0,2),(0,3),(1,2),(1,3)}
    assert Counter(h.weight for h in hs)==Counter([F(1,6),F(1,6),F(1,3),F(1,3)])
    assert all(h.tree[1]=='Fork_2' and h.chronology==('a','b') for h in hs)
    assert {h.cost for h in hs}=={(1,1),(1,2),(2,1),(2,2)}
    return {'Fork_0_paths':len(empty),'Fork_2_paths':len(hs),'qualification':'Algebraic batch fixtures and declared token partitions; not a full type checker.'}

def coupling_composition():
    ps=[F(1,4),F(1,4),F(1,2),F(0)]
    cs=[4,2,7,9];r=[0,0,1,1];qs=[F(1,2),F(1,2)];ds=[2,6]
    trees=[node('outer0',leaf(0)),node('outer1',leaf(1),leaf(0))]
    source=[H(p,(c,0),trees[r[i]],()) for i,(p,c) in enumerate(zip(ps,cs))]
    target=[H(p,(c,0),trees[i],()) for i,(p,c) in enumerate(zip(qs,ds))]
    def source_child(x):
        return [H(F(1,3),(3,1),node('read',leaf(x)),('read',)),
                H(F(2,3),(2,1),node('read',leaf(x)),('read',))]
    def target_child(x):return [H(F(1),(1,0),node('read',leaf(x)),('read',))]
    ss=bind(source,source_child);tt=bind(target,target_child)
    normalized(ss);normalized(tt)
    target_marginal=defaultdict(F)
    mapped=0
    for i,outer in enumerate(source):
        bs=leaves(outer.tree)
        for children in product(*(source_child(x) for x in bs)):
            w=outer.weight
            for z in children:w*=z.weight
            src_cost=add(outer.cost,*(z.cost for z in children))
            tgt_cost=(ds[r[i]]+len(bs),0)
            tgt_tree=graft(outer.tree,[node('read',leaf(x)) for x in bs])
            assert all(a>=b for a,b in zip(src_cost,tgt_cost))
            assert graft(outer.tree,[z.tree for z in children])==tgt_tree
            target_marginal[(tgt_cost,tgt_tree)]+=w;mapped+=1
    assert {k:v for k,v in target_marginal.items() if v}==law(tt)
    assert mapped==len(ss)==12
    bounds=0
    for b1,b2 in product(range(15),range(4)):
        sp=sum((h.weight for h in ss if h.cost[0]<=b1 and h.cost[1]<=b2),F())
        tp=sum((h.weight for h in tt if h.cost[0]<=b1 and h.cost[1]<=b2),F())
        assert tp>=sp;bounds+=1
    return {'raw_source_composite_paths':len(ss),'raw_target_composite_paths':len(tt),'tested_budget_bounds':bounds,'coupling_target_marginal':'correct'}

if __name__=='__main__':
    result={'fixture':fixture(),'associativity':associativity(),'chronology':chronology(),'zero_path':zero_path(),'native_coupling':native_coupling(),'batch':batch_fixtures(),'coupling_composition':coupling_composition(),'status':'passed','qualification':'Finite regression fixtures, not a formal proof of the general theorems.'}
    print(json.dumps(result,indent=2))
