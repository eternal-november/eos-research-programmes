#!/usr/bin/env python3
"""Independent finite O4 AST regression, not a general typechecker/formal proof.

Pointwise Γ semantics: evaluator carries public env to every actual Bind hole;
only that hole's capability tuple is supplied to its continuation. Comparing
reindexed runs forgets Γ's outer tag on BOTH sides, retaining full typed leaves.
All finite raw witnesses, including weight zero, are evaluated and checked.
Call is administrative. Pure expressions are finite table/variable/product ASTs;
no claim is made here to test the note's entire pure lambda calculus.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import product
from collections import defaultdict
import json
from pathlib import Path

@dataclass(frozen=True)
class V: name: str
@dataclass(frozen=True)
class K: value: object
@dataclass(frozen=True)
class Pair: left: object; right: object
@dataclass(frozen=True)
class Tab: entries: tuple; arg: object

def pe(e, env, current):
    if isinstance(e,V): return current if e.name=='$' else env[e.name]
    if isinstance(e,K): return e.value
    if isinstance(e,Pair): return (pe(e.left,env,current),pe(e.right,env,current))
    if isinstance(e,Tab): return dict(e.entries)[pe(e.arg,env,current)]
    raise TypeError(e)

def ordinary_parameter(e):
    # Procedure parameter substitutions are Γ terms, not dynamic input-slot
    # expressions. Inputs are supplied separately as current configurations.
    if isinstance(e,V): return e.name != '$'
    if isinstance(e,K): return True
    if isinstance(e,Pair): return ordinary_parameter(e.left) and ordinary_parameter(e.right)
    if isinstance(e,Tab): return ordinary_parameter(e.arg)
    raise TypeError(e)

def ps(e,sigma):
    if isinstance(e,V): return sigma.get(e.name,e)
    if isinstance(e,K): return e
    if isinstance(e,Pair): return Pair(ps(e.left,sigma),ps(e.right,sigma))
    if isinstance(e,Tab): return Tab(e.entries,ps(e.arg,sigma))
    raise TypeError(e)

@dataclass(frozen=True)
class Cfg: public: object; caps: tuple=()
@dataclass(frozen=True)
class Ret: value: object
@dataclass(frozen=True)
class Op: name: str; arg: object=K(None)
@dataclass(frozen=True)
class Bind: first: object; then: object
@dataclass(frozen=True)
class Case: selector: object; branches: tuple
@dataclass(frozen=True)
class Call: name: str; args: tuple
@dataclass(frozen=True)
class Batch: children: tuple; split: tuple
@dataclass(frozen=True)
class Run:
    p: Q; cost: int; tree: tuple; choices: tuple=(); chronology: tuple=()

class Reject(Exception): pass

def cs(t,sigma):
    """Γ substitution; $ is the distinguished current-input slot, never Γ."""
    assert '$' not in sigma
    if isinstance(t,Ret): return Ret(ps(t.value,sigma))
    if isinstance(t,Op): return Op(t.name,ps(t.arg,sigma))
    if isinstance(t,Bind): return Bind(cs(t.first,sigma),cs(t.then,sigma))
    if isinstance(t,Case): return Case(ps(t.selector,sigma),tuple((k,cs(v,sigma)) for k,v in t.branches))
    if isinstance(t,Call): return Call(t.name,tuple((k,ps(v,sigma)) for k,v in t.args))
    if isinstance(t,Batch): return Batch(tuple(cs(c,sigma) for c in t.children),t.split)
    raise TypeError(t)

def plug(t,impl):
    if isinstance(t,Call):
        if not all(ordinary_parameter(v) for _,v in t.args): raise Reject('call parameters must be Γ terms')
        return cs(impl[t.name],dict(t.args))
    if isinstance(t,Bind): return Bind(plug(t.first,impl),plug(t.then,impl))
    if isinstance(t,Case): return Case(t.selector,tuple((k,plug(v,impl)) for k,v in t.branches))
    if isinstance(t,Batch): return Batch(tuple(plug(c,impl) for c in t.children),t.split)
    return t

def leaves(tree):
    return [tree[1]] if tree[0]=='hole' else [c for child in tree[2] for c in leaves(child)]

def graft(tree, replacements):
    if tree[0]=='hole': return next(replacements)
    return ('node',tree[1],tuple(graft(c,replacements) for c in tree[2]))

def need(c,kind):
    if c.caps != (('r',kind),): raise Reject(f'requires r:{kind}; got {c.caps}')

def outcomes(name,arg,c):
    """Declared finite primitive tables: witness ID, weight, cost, outputs."""
    if name=='check':
        need(c,'Probe')
        return [('pass',Q(arg),1,[Cfg(('Pass',True),(('r','Approved'),))]),
                ('fail',1-Q(arg),2,[Cfg(('Fail',False),(('r','Rejected'),))])]
    if name in ('commit','release'):
        need(c, 'Approved' if name=='commit' else 'Rejected')
        if name=='commit' and c.public != ('Pass',True): raise Reject('missing matching public evidence')
        return [('done',Q(1),1,[Cfg((name,arg))])]
    if name=='simulate':
        if c.caps: raise Reject('fixture simulator has empty input interface')
        return [('no',Q(1,2),0,[Cfg(False)]),('yes',Q(1,2),0,[Cfg(True)])]
    if name=='act':
        need(c,'Ready')
        return [('done',Q(1),1,[Cfg('acted')])]
    if name=='fork':
        if c.caps: raise Reject('fixture fork has empty ownership')
        return [('two',Q(1),0,[Cfg(0),Cfg(1)])]
    if name in ('a','b','c'):
        return [('unit',Q(1),1,[c])]
    if name=='zero':
        return [('live',Q(1),0,[c]),('zero',Q(0),9,[c])]
    if name=='live': return [('live',Q(1),0,[c])]
    raise Reject('unknown primitive '+name)

def ev(t,env,c,impl):
    if isinstance(t,Ret): return [Run(Q(1),0,('hole',Cfg(pe(t.value,env,c.public),c.caps)))]
    if isinstance(t,Op):
        rows=outcomes(t.name,pe(t.arg,env,c.public),c)
        assert sum(r[1] for r in rows)==1
        result=[]
        for wid,p,cost,outs in rows:
            ids=[i for out in outs for i,_ in out.caps]
            if len(ids)!=len(set(ids)) or not set(ids)<=set(i for i,_ in c.caps):
                raise Reject('primitive creates or duplicates ownership')
            # zero/live intentionally same public label: equality-level witness.
            label='sample' if t.name in ('zero','live') else t.name
            result.append(Run(p,cost,('node',label,tuple(('hole',x) for x in outs)),(wid,),(t.name,)))
        return result
    if isinstance(t,Case): return ev(dict(t.branches)[pe(t.selector,env,c.public)],env,c,impl)
    if isinstance(t,Call):
        if not all(ordinary_parameter(v) for _,v in t.args): raise Reject('call parameters must be Γ terms')
        actual={k:pe(v,env,c.public) for k,v in t.args}
        return ev(impl[t.name],actual,c,impl)
    if isinstance(t,Bind):
        out=[]
        for r in ev(t.first,env,c,impl):
            # env persists; each child receives ONLY its own returned caps.
            for rs in product(*(ev(t.then,env,d,impl) for d in leaves(r.tree))):
                p=r.p
                for q in rs: p*=q.p
                out.append(Run(p,r.cost+sum(q.cost for q in rs),
                    graft(r.tree,iter(q.tree for q in rs)),
                    r.choices+tuple(q.choices for q in rs),
                    r.chronology+sum((q.chronology for q in rs),())))
        return out
    if isinstance(t,Batch):
        if len(t.split)!=len(t.children): raise Reject('bad split arity')
        ids=sum(t.split,())
        if len(ids)!=len(set(ids)) or set(ids)!=set(i for i,_ in c.caps): raise Reject('split must partition ownership')
        contexts=[Cfg(c.public,tuple(x for x in c.caps if x[0] in s)) for s in t.split]
        out=[]
        for rs in product(*(ev(ch,env,d,impl) for ch,d in zip(t.children,contexts))):
            p=Q(1)
            for r in rs:p*=r.p
            out.append(Run(p,sum(r.cost for r in rs),('node','Fork_'+str(len(rs)),tuple(r.tree for r in rs)),
                           tuple(r.choices for r in rs),sum((r.chronology for r in rs),())))
        return out
    raise TypeError(t)

def law(rs):
    d=defaultdict(Q)
    for r in rs:d[(r.cost,r.tree)]+=r.p
    return {k:v for k,v in d.items() if v}

def expect_reject(f):
    try:f()
    except Reject:return
    raise AssertionError('invalid fixture accepted')

def main():
    stats={}
    bit=Tab(((0,1),(1,0)),V('z'))
    pure=[V('x'),Pair(V('x'),V('y')),Tab(((0,'L'),(1,'H')),V('x'))]
    substitutions=[{'x':K(i),'y':K(j)} for i,j in product(range(2),repeat=2)]
    substitutions += [{'x':V('z'),'y':bit},{'x':bit,'y':V('z')}]
    n=0
    for s,e,z in product(substitutions,pure,range(2)):
        env={'z':z}; actual={k:pe(v,env,None) for k,v in s.items()}
        assert pe(ps(e,s),env,None)==pe(e,actual,None);n+=1
    stats['pure_substitution_cases']=n
    branch=Case(Tab(((('Pass',True),'Pass'),(('Fail',False),'Fail')),V('$')),
                (('Pass',Op('commit',V('stamp'))),('Fail',Op('release',V('stamp')))))
    call=Call('checkproc',(('p',V('x')),))
    impl={'checkproc':Op('check',V('p'))}
    client=Bind(call,branch)
    # Include administrative Call, dependent Case, Ret, Batch and multi-hole Bind.
    terms=[Ret(Pair(V('x'),V('$'))),Op('check',V('x')),client,
           Bind(Op('fork'),Ret(Pair(V('stamp'),V('$')))),
           Batch((Ret(V('x')),Bind(Op('simulate'),Ret(Pair(V('stamp'),V('$'))))),((),()))]
    count=0; plugcount=0; reindexed_contexts=set()
    for p,stamp in product((Q(0),Q(1,3),Q(1)),('A','B')):
        sigma={'x':K(p),'stamp':K(stamp)}
        for t in terms:
            cfg=Cfg('in',(('r','Probe'),)) if t in terms[1:3] else Cfg('in')
            a=ev(cs(t,sigma),{},cfg,impl)
            b=ev(t,{'x':p,'stamp':stamp},cfg,impl)
            assert a==b;count+=1
            assert ev(plug(cs(t,sigma),impl),{},cfg,{})==a;plugcount+=1
            if t==terms[1]:
                assert len(a)==2 # raw zero witnesses must survive endpoints p=0,1
                reindexed_contexts.update(d.caps for r in a for d in leaves(r.tree))
    assert reindexed_contexts=={(('r','Approved'),),(('r','Rejected'),)}
    # Nonconstant reindexing plus nontrivial implementation bodies exercise
    # table substitution through Call and Bind, not only literal replacement.
    parameter_table=Tab(((0,Q(0)),(1,Q(1,3)),(2,Q(1))),V('z'))
    stamp_table=Tab(((0,'A'),(1,'B'),(2,'A')),V('z'))
    rich_impl={'checkproc':Bind(Op('check',V('p')),Ret(V('$')))}
    for z in range(3):
        sigma={'x':parameter_table,'stamp':stamp_table}
        env={'z':z}
        actual={k:pe(v,env,None) for k,v in sigma.items()}
        cfg=Cfg('in',(('r','Probe'),))
        instantiated=cs(client,sigma)
        reference=ev(client,actual,cfg,rich_impl)
        assert ev(instantiated,env,cfg,rich_impl)==reference;count+=1
        assert ev(plug(instantiated,rich_impl),env,cfg,{})==reference;plugcount+=1
        # Pure substitution and plugging commute as syntax in this core.
        assert plug(cs(client,sigma),rich_impl)==cs(plug(client,rich_impl),sigma)
    stats.update(command_substitution_cases=count,procedure_plugging_cases=plugcount,
                 dependent_post_kinds=['Approved','Rejected'],zero_witness_retained=True)
    # Γ indexes the input kind itself: reindex x=b and E(x)=r:kind(x).
    dependent=Case(V('x'),((0,Op('release')),(1,Op('commit'))))
    for z in (0,1):
        c=Cfg(('Pass',True) if z else ('Fail',False),(('r','Approved' if z else 'Rejected'),))
        assert ev(cs(dependent,{'x':bit}),{'z':1-z},c,{})==ev(dependent,{'x':z},c,{})
    stats['dependent_input_reindex_cases']=2
    invalid=[lambda:ev(Batch((call,call),(('r',),('r',))),{'x':Q(1)},Cfg('in',(('r','Probe'),)),impl),
             lambda:ev(Bind(client,call),{'x':Q(1),'stamp':'A'},Cfg('in',(('r','Probe'),)),impl),
             lambda:ev(Bind(Op('simulate'),Op('act')),{},Cfg(('model','evidence')),{}),
             lambda:ev(Op('commit'),{},Cfg(('Pass',True)),{}),
             lambda:ev(Op('commit'),{},Cfg(('Fail',False),(('r','Approved'),)),{}),
             # Zero-weight Fail is still checked: cannot commit on every branch.
             lambda:ev(Bind(Op('check',K(1)),Op('commit')),{},Cfg('in',(('r','Probe'),)),{})]
    for f in invalid: expect_reject(f)
    stats['resource_type_rejections']=len(invalid)
    c=Cfg('end')
    ab=ev(Bind(Op('a'),Op('b')),{},c,{})
    ba=ev(Bind(Op('b'),Op('a')),{},c,{})
    assert law(ab)!=law(ba) and leaves(ab[0].tree)==leaves(ba[0].tree) and ab[0].cost==ba[0].cost
    stats['event_exchange_rejected']=True
    zero=ev(Op('zero'),{},c,{})
    live=ev(Op('live'),{},c,{})
    assert law(zero)==law(live) and len(zero)!=len(live)
    assert not all(r.cost<=1 for r in zero) and all(r.cost<=1 for r in live)
    # Exact native inclusion live -> zero: singleton maps to live branch; target
    # empty fibre has probability 0 and cost9 <= infinity. No raw inverse.
    assert live[0].p==zero[0].p and live[0].cost==zero[0].cost and live[0].tree==zero[0].tree
    stats['law_equality_not_raw_budget_equality']=True
    # Phase-Bind association: equal causal/cost laws, different chronological words.
    left=ev(Bind(Bind(Op('fork'),Op('a')),Op('b')),{},c,{})
    right=ev(Bind(Op('fork'),Bind(Op('a'),Op('b'))),{},c,{})
    assert law(left)==law(right) and left[0].chronology!=right[0].chronology
    stats['associativity_chronology_counterexample']=[left[0].chronology,right[0].chronology]
    stats['scope']='Finite AST regression, exact rational arithmetic; not a full typechecker or formal proof. Covers finite pure tables/products, not all lambda/evidence constructors.'
    stats['status']='PASS'
    output=Path(__file__).with_name('o4_substitution_results.json')
    output.write_text(json.dumps(stats,indent=2)+'\n')
    print(json.dumps(stats,indent=2))
if __name__=='__main__':main()
