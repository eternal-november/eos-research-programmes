"""Compile evidence separately from claims and replay all benchmark verdicts."""
from hashlib import sha256
from itertools import product
from random import Random
import json
from pathlib import Path
from reuse import Graph,Edits,Fact,Observation,full,update,witnesses,validate_path,infer
from direct_incremental import update_with_witnesses
from scenarios import instances,a,d,uncertain_alias,splicing,invalid_union,large,cost_cases

LABELS=('safety','deadline')

def preds(g):
    R=set(g.roots)
    while True:
        S=R|{v for x in R for v in g.out[x]}
        if S==R:
            return R
        R=S

def facts(g,R):
    seen={}
    k=set()
    for state in R:
        f=g.facts[state]
        k|=f.bad
        if f.obs:
            key=f.obs[:3]
            seen.setdefault(key,set()).add(f.obs.action)
    if any(len(o)>1 for o in seen.values()):
        k.add('realizability')
    return k

def check_witness(g,p,name):
    if p is None:
        return
    if name=='realizability':
        x,y=p
        assert validate_path(g,x) and validate_path(g,y)
        a,b=g.facts[x[-1]].obs,g.facts[y[-1]].obs
        assert a[:3]==b[:3] and a.action!=b.action
    else:
        assert validate_path(g,p) and name in g.facts[p[-1]].bad

def checked(old,e,c=None):
    if c is None:c,_=full(old)
    new,proof,m=update(old,c,e)
    matched,q,b=update_with_witnesses(old,c,e)
    cold,s=full(new)
    expected=preds(new);truth=facts(new,expected)
    assert set(proof.parent)==set(q.parent)==set(cold.parent)==expected
    W=witnesses(proof,LABELS)
    for cert in (proof,q,cold):
        assert {k for k,w in witnesses(cert,LABELS).items() if w is not None}==truth
        for k,w in witnesses(cert,LABELS).items():
            check_witness(new,w,k)
    # Rooted witnesses for all states, including those not selected for failures.
    for r,p in proof.parent.items():
        assert (r in new.roots if p is None else r in new.out[p])
    return new,proof,W,{'cone':m,'witness_worklist':b,'cold':s}

out={}
for name,old,e,should in instances:
    new,p,w,cost=checked(old,e)
    assert {k for k,v in w.items() if v is not None}==should
    out[name]=dict(witnesses=w,cost=cost)

def possible(old,patches,queries):
    c,_=full(old)
    W={name:checked(old,e,c)[2]['safety'] for name,e in patches.items()}
    # The query map supplies named outcomes and costs; the tool never
    # pretends it has independently sensed which installation is present.
    mixed={}
    for name,(cost,values) in queries.items():
        assert set(values)==set(W)
        groups={}
        for z,outcome in values.items():
            groups.setdefault(outcome,{})[z]=W[z]
        mixed[name]=[k for k,g in groups.items() if infer(g)=='undecided']
    choices=sorted((queries[name][0],name) for name,v in mixed.items() if not v)
    return dict(judgment=infer(W),by_installation=W,
                separating_one_query=choices[0] if choices else None,
                unresolved_replies=mixed)

out['unknown_alias']=possible(a,uncertain_alias,{
 'older inbox read':(1,{'independent':'accepted','shared':'accepted'}),
 'diagnostic and cancel name same spend pool':(2,{'independent':'no','shared':'yes'}),
 'exact trace of pre-cancel resource ledger':(4,{'independent':'1','shared':'0'}),
})
assert out['unknown_alias']['judgment']=='undecided'
assert out['unknown_alias']['separating_one_query'][0]==2
out['branchwise_law_not_edgewise']=possible(d,splicing,{})
out['fictional_union_control']=checked(d,invalid_union)[2]['safety']
assert out['branchwise_law_not_edgewise']['judgment']=='carries'
assert out['fictional_union_control']==['start','port','unsafe']
seq,cache,*_=checked(d,splicing['law0'])
cumulative=checked(seq,splicing['law1'],cache)[2]['safety']
assert cumulative==out['fictional_union_control']
out['same_edits_actually_admitted_together']=cumulative
cost={name:checked(large,e)[3] for name,e in cost_cases.items()}

from plant import Mode,compile as plant,patch
plant_rows={}
baseline=plant(Mode(False,False))
for alias,late in product((False,True),repeat=2):
    new=plant(Mode(alias,late))
    p=patch(baseline,new)
    tested,c,found,costs=checked(baseline,p)
    assert {k for k,v in found.items() if v is not None}==(
        ({'safety'} if alias else set())|({'deadline'} if late else set()))
    assert tested.out==new.out and tested.facts==new.facts
    plant_rows[f'shared={alias},slow={late}']=dict(witnesses=found,check=costs,
          compiler_diff_rows_read=len(baseline.out)*4,edit_out_rows=len(p.out))
out['compiled_fixed_policy_plant']=plant_rows

rng=Random(97218)
checks=0
for n in range(1,17):
    for density in (0.0,.08,.2,.55):
        for i in range(60):
            X=[f'{j:02d}' for j in range(n)]
            random_row=lambda: frozenset(j for j in X if rng.random()<density)
            random_fact=lambda: Fact(frozenset(z for z in LABELS if rng.randrange(5)==0),
                 (Observation('a','cut',str(rng.randrange(3)),str(rng.randrange(3)))
                     if rng.randrange(3)==0 else None))
            baseline=Graph(frozenset(j for j in X if rng.randrange(7)==0),
                           {j:random_row() for j in X},{j:random_fact() for j in X})
            c,_=full(baseline)
            for step in range(2):
                edit=Edits(roots=(None if rng.randrange(2)==0 else random_row()),
                           out={j:random_row() for j in X if rng.randrange(5)==0},
                           facts={j:random_fact() for j in X if rng.randrange(4)==0})
                baseline,c,*_=checked(baseline,edit,c)
                checks+=1
h={s:sha256(Path(__file__).with_name(s).read_bytes()).hexdigest() for s in ('FREEZE.txt','reuse.py')}
print(json.dumps(dict(freeze=h,verdicts=out,measured_work=cost,deterministic_patch_checks=checks),
                 sort_keys=True,indent=2))
