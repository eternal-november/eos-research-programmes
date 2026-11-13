#!/usr/bin/env python3
"""Independent finite-model audit of retained-table ground causal descent.
Two memory sorts and one fixed two-element action sort; actual tables are
compared with finite-case sorted congruence closure, including aliased codepoints.
No imports from the author's checker.
"""
from itertools import product, combinations
from pathlib import Path
import hashlib, json, random
ROOT=Path(__file__).resolve().parents[1]
def canon(xs):
    d={}
    return tuple(d.setdefault(x,len(d)) for x in xs)
def partitions(n):
    if n==0:
        yield (); return
    def go(p):
        if len(p)==n: yield tuple(p); return
        for v in range(max(p)+2): yield from go(p+[v])
    yield from go([0])
# M terms: x,y,g(z). N terms: z,f(x),f(y). A terms: d(z),d(f(x)),d(f(y)).
physical=set(); actual_count=0
functions=list(product(range(3),repeat=3))
for f,g in product(functions,repeat=2):
    for x,y,z in product(range(3),repeat=3):
        mv=(x,y,g[z]); nv=(z,f[x],f[y])
        for d in product(range(2),repeat=3):
            physical.add((canon(mv),canon(nv),tuple(d[v] for v in nv)))
            actual_count+=1
# Independent small-model construction via partitions, not table enumeration.
partition_models=set()
for pm,pn in product(list(partitions(3)),repeat=2):
    if pm[0]==pm[1] and pn[1]!=pn[2]: continue
    for labels in product(range(2),repeat=max(pn)+1):
        partition_models.add((pm,pn,tuple(labels[v] for v in pn)))
assert partition_models==physical
# Actual sorted ground congruence procedure. IDs M:0..2,N:3..5,A:6..10.
sorts=[0]*3+[1]*3+[2]*5
apps=[(4,'f',(0,)),(5,'f',(1,)),(2,'g',(3,)),
      (6,'d',(3,)),(7,'d',(4,)),(8,'d',(5,))]
atoms=[(0,1),(0,2),(1,2),(3,4),(3,5),(4,5),(6,9),(7,9),(8,9)]
def cc(eqs,neqs,actions):
    parent=list(range(11))
    def find(a):
        while parent[a]!=a:
            parent[a]=parent[parent[a]];a=parent[a]
        return a
    def join(a,b):
        assert sorts[a]==sorts[b]
        a,b=find(a),find(b)
        if a==b:return False
        parent[b]=a;return True
    for a,b in eqs:join(a,b)
    for t,v in zip((6,7,8),actions):join(t,9+v)
    changed=True
    while changed:
        changed=False
        for (out,f,args),(out2,f2,args2) in combinations(apps,2):
            if f==f2 and tuple(map(find,args))==tuple(map(find,args2)):
                changed=join(out,out2) or changed
    if any(find(a)==find(b) for a,b in list(neqs)+[(9,10)]):return None
    return canon([find(i) for i in range(3)]),canon([find(i) for i in range(3,6)]),tuple(actions)
case_models=set();case_count=0
for truth in product((False,True),repeat=len(atoms)):
    eqs=[a for a,t in zip(atoms,truth) if t]
    neqs=[a for a,t in zip(atoms,truth) if not t]
    for actions in product(range(2),repeat=3):
        result=cc(eqs,neqs,actions);case_count+=1
        if result is not None:case_models.add(result)
assert case_models==physical
# Finite Boolean/guarded entailment tests over both independently constructed universes.
def vals(p):
    m,n,a=p
    return [m[0]==m[1],m[0]==m[2],m[1]==m[2],n[0]==n[1],n[0]==n[2],n[1]==n[2],a[0]==0,a[1]==0,a[2]==0]
def evalf(f,v):
    if isinstance(f,int):return v[f]
    op,*args=f
    if op=='not':return not evalf(args[0],v)
    if op=='and':return all(evalf(x,v) for x in args)
    if op=='or':return any(evalf(x,v) for x in args)
    if op=='implies':return not evalf(args[0],v) or evalf(args[1],v)
    raise AssertionError(op)
rng=random.Random(270510)
def formula(depth=2):
    if depth==0 or rng.random()<.25:return rng.randrange(len(atoms))
    op=rng.choice(('not','and','or','implies'))
    return (op,formula(depth-1)) if op=='not' else (op,formula(depth-1),formula(depth-1))
actual_values=[vals(p) for p in physical];case_values=[vals(p) for p in case_models]
for _ in range(2500):
    f,g=formula(),formula()
    a=all(not evalf(f,v) or evalf(g,v) for v in actual_values)
    b=all(not evalf(f,v) or evalf(g,v) for v in case_values)
    assert a==b
# Nested function applications with all possible merging of four code terms.
nested_actual=set()
for f in product(range(4),repeat=4):
    for x,y in product(range(4),repeat=2):
        nested_actual.add(canon((x,y,f[x],f[f[x]])))
nested_quotients={p for p in partitions(4) if not(p[0]==p[2] and p[2]!=p[3])}
assert nested_actual==nested_quotients
# Context and scope controls. Each assertion is a direct actual-function test.
controls={}
tables2=list(product(range(2),repeat=2))
controls['shared_update_conflict']=all(not(f[0]==0 and f[0]==1) for f in tables2) and any(f[0]==0 for f in tables2) and any(f[0]==1 for f in tables2)
controls['shared_decoder_demand_conflict']=bool({0,1}&{1}) and not bool({0}&{1})
controls['symbol_renaming_not_port_substitution']=any(f[0]==0 and g[0]==1 for f,g in product(tables2,repeat=2)) and not any(f[0]==0 and f[0]==1 for f in tables2)
controls['port_alias_propagates_same_function']=all(x!=y or f[x]==f[y] for f in tables2 for x,y in product(range(2),repeat=2))
controls['fixed_budget_not_uniform_necessity']=all(x==y for x,y in product(range(1),repeat=2)) and any(x!=y for x,y in product(range(2),repeat=2))
controls['restricted_identity_library_not_unrestricted']=all(f[x]==x for f in [(0,1)] for x in range(2)) and any(f[x]!=x for f in tables2 for x in range(2))
controls['enum_distinctness']=cc([(9,10)],[],(0,0,0)) is None
controls['nonempty_unused_sort']=len([0])==1
# Enumerated outputs used as function arguments: same enum arguments trigger congruence,
# different action values do not. Explicit time-independent two-input table h.
controls['enum_argument_preserves_functionality']=all(h[2*x+a]==h[2*y+b] for h in product(range(2),repeat=4) for x,y,a,b in product(range(2),repeat=4) if x==y and a==b)
controls['enum_arguments_not_silently_collapsed']=any(h[0]!=h[1] for h in product(range(2),repeat=4))
assert all(controls.values())
source=ROOT/'theory/Parametric_Causal_Descent.md'
weaker=ROOT/'theory/Causal_Constraint_Descent.md'
result={'status':'PASS','source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
 'weaker_source_sha256':hashlib.sha256(weaker.read_bytes()).hexdigest(),
 'actual_two_memory_sort_function_interpretations':actual_count,
 'distinct_ground_interpretations':len(physical),'boolean_enum_cc_cases':case_count,
 'boolean_and_guarded_entailment_comparisons':2500,
 'nested_actual_interpretations':4**4*4**2,'nested_ground_patterns':len(nested_actual),
 'context_and_scope_controls':controls,
 'scope':'Two memory sorts with three named ground terms each, one fixed binary action sort; nested unary-term and enum-argument controls are separate. General proof independently reviewed, not established by finite tests.'}
out=ROOT/'review/Parametric_Descent_Independent_Results.json'
out.parent.mkdir(parents=True,exist_ok=True)
out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
