#!/usr/bin/env python3
"""Exact finite O4 regression checks, not a general type checker or formal proof."""
from collections import defaultdict
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
import json

FUNS = tuple(product((0, 1), repeat=2))

def add_mass(d, key, mass):
    d[key] += mass

def clean(d): return {k:v for k,v in d.items() if v}
def stop(v=0): return ('stop', v)
def ask(a, zero, one): return ('ask', a, zero, one)

@lru_cache(None)
def bounded_clients(depth):
    if depth == 0: return (stop(0), stop(1))
    sub = bounded_clients(depth-1)
    return (stop(0),stop(1)) + tuple(ask(a,s0,s1) for a in (0,1) for s0 in sub for s1 in sub)

@lru_cache(None)
def full_query_clients(depth):
    if depth == 0: return (stop(0),)
    sub = full_query_clients(depth-1)
    return tuple(ask(a,s0,s1) for a in (0,1) for s0 in sub for s1 in sub)

def direct_function(client, f, remaining, transcript=()):
    if client[0] == 'stop':
        return (transcript, len(transcript), remaining, client[1])
    if remaining == 0: raise ValueError('No call rule at Ready_0')
    a = client[1]
    b = f[a]
    return direct_function(client[2+b], f, remaining-1, transcript+((a,b),))

def direct_law(client, mu, horizon):
    out=defaultdict(F)
    for f,mass in zip(FUNS,mu):
        add_mass(out,direct_function(client,f,horizon),mass)
    return clean(out)

def service_law(client, mu, horizon):
    # Independently evaluate a private store / public credit machine.
    todo=[(mass,client,{'service': f},horizon,(),0) for f,mass in zip(FUNS,mu)]
    out=defaultdict(F)
    while todo:
        mass,term,store,credit,tr,cost=todo.pop()
        if term[0]=='stop':
            add_mass(out,(tr,cost,credit,term[1]),mass)
            continue
        if credit==0:raise ValueError('No call rule at Ready_0')
        a=term[1]
        old_state=store['service']
        b=old_state[a]
        # The state is retained, not freshly sampled from the public marginal.
        next_store={'service': old_state}
        todo.append((mass,term[2+b],next_store,credit-1,tr+((a,b),),cost+1))
    return clean(out)

def mix(laws, weights):
    out=defaultdict(F)
    for law,w in zip(laws,weights):
        for value,p in law.items():add_mass(out,value,w*p)
    return clean(out)

def adaptive_equivalence():
    mus=[(F(1,4),)*4,(F(1),F(0),F(0),F(0)),
         (F(0),F(1,3),F(1,6),F(1,2)),(F(1,10),F(2,10),F(3,10),F(4,10))]
    checked=0
    # All stop/query controllers of horizon two; full query controllers of horizon three.
    families=[(2,bounded_clients(2)),(3,full_query_clients(3))]
    for horizon,clients in families:
        for client in clients:
            for mu in mus:
                left=direct_law(client,mu,horizon)
                right=service_law(client,mu,horizon)
                assert left==right
                assert sum(left.values(),F())==1
                checked+=1
    first,last=bounded_clients(2)[1],bounded_clients(2)[-1]
    mu=mus[-1]
    assert mix([direct_law(first,mu,2),direct_law(last,mu,2)],[F(2,5),F(3,5)])==mix([service_law(first,mu,2),service_law(last,mu,2)],[F(2,5),F(3,5)])
    adaptive=ask(0,ask(1,stop(),stop()),ask(0,stop(),stop()))
    law=direct_law(adaptive,(F(1,4),)*4,2)
    responses=defaultdict(F)
    for (tr,_,_,_),mass in law.items():add_mass(responses,tuple(b for _,b in tr),mass)
    assert clean(responses)=={(0,0):F(1,4),(0,1):F(1,4),(1,1):F(1,2)}
    return {'controllers_with_stopping_depth_2':len(bounded_clients(2)),
            'full_query_controllers_depth_3':len(full_query_clients(3)),
            'initial_function_laws':len(mus),'controller_law_cases':checked,
            'randomized_client_mixture_checked':True,
            'adaptive_response_law':{'00':'1/4','01':'1/4','10':'0','11':'1/2'}}

def bernoulli_pair(p):
    return {(a,b):(p if a else 1-p)*(p if b else 1-p) for a,b in product((0,1),repeat=2)}

def protocols():
    shared={(0,0):F(1,2),(1,1):F(1,2)}
    chosen=mix([bernoulli_pair(F(1,4)),bernoulli_pair(F(3,4))],[F(1,2),F(1,2)])
    fresh=bernoulli_pair(F(1,2))
    reselected=defaultdict(F)
    for p,q in product((F(1,4),F(3,4)),repeat=2):
        for a,b in product((0,1),repeat=2):
            add_mass(reselected,(a,b),F(1,4)*(p if a else 1-p)*(q if b else 1-q))
    assert clean(reselected)==fresh
    assert chosen=={(0,0):F(5,16),(0,1):F(3,16),(1,0):F(3,16),(1,1):F(5,16)}
    agreements=[]
    for law in (shared,chosen,fresh):
        assert sum(law.values(),F())==1
        for i in (0,1):assert sum(p for pair,p in law.items() if pair[i]==1)==F(1,2)
        agreements.append(sum(p for pair,p in law.items() if pair[0]==pair[1]))
    assert agreements==[F(1),F(5,8),F(1,2)]
    return {'sampled_function_or_stored_service_agreement':str(agreements[0]),
            'once_selected_random_kernel_agreement':str(agreements[1]),
            'fresh_fair_kernel_agreement':str(agreements[2]),
            'reselect_kernel_each_call_equals_fresh':True,
            'one_call_marginals_all_fair':True}

def leaf(x):return ('leaf',x)
def node(label,*children):return ('node',label,tuple(children))
def holes(t):
    return 1 if t[0]=='leaf' else sum(map(holes,t[2]))
def graft(t,replacements):
    it=iter(replacements)
    def go(s):
        if s[0]=='leaf':return next(it)
        return node(s[1],*(go(c) for c in s[2]))
    out=go(t)
    try:next(it)
    except StopIteration:return out
    raise ValueError('Too many replacements')
def erase_private(t):
    if t[0]=='leaf':return t
    children=tuple(map(erase_private,t[2]))
    if str(t[1]).startswith('_'):
        if len(children)!=1:raise ValueError('Only unary private nodes are erased')
        return children[0]
    return node(t[1],*children)

def erasure():
    trees=[leaf(0),node('_init',leaf(0)),node('call',node('_read',leaf(0))),
           node('fork',leaf(0),node('_read',leaf(1))),node('stop'),
           node('_init',node('fork',node('_read',leaf(0)),leaf(1)))]
    inserted=[leaf(7),node('_read',leaf(8)),node('call',leaf(9)),node('stop')]
    cases=0
    for t in trees:
        for subs in product(inserted,repeat=holes(t)):
            assert erase_private(graft(t,subs))==graft(erase_private(t),tuple(map(erase_private,subs)))
            cases+=1
    fun=node('_init_function',node('call(0,1)',node('call(1,0)',leaf('done'))))
    svc=node('_init_service',node('_read',node('call(0,1)',node('_read',node('call(1,0)',leaf('done'))))))
    assert fun!=svc and erase_private(fun)==erase_private(svc)
    try:erase_private(node('_bad_binary',leaf(0),leaf(1)))
    except ValueError:rejected=True
    else:rejected=False
    assert rejected
    return {'graft_commutation_cases':cases,'different_management_trees_equal_after_erasure':True,'private_nonunary_erasure_rejected':True}

def resources():
    def call(token):
        name,n=token
        if n==0:raise ValueError('Exhausted')
        return name,n-1
    initial=('r',2)
    after1=call(initial);after2=call(after1)
    assert after1==('r',1) and after2==('r',0)
    try:call(after2)
    except ValueError:exhausted=True
    else:exhausted=False
    def valid_split(parts):
        return sum(map(len,parts))==len(set().union(*parts))
    assert not valid_split(({'r'},{'r'}))
    assert valid_split(({'r'},{'s'}))
    def reusable_code_capture_allowed(captured_capabilities):return len(captured_capabilities)==0
    assert reusable_code_capture_allowed(set())
    assert not reusable_code_capture_allowed({'r'})
    assert exhausted
    return {'same_token_threaded_two_calls':True,'third_call_rejected':True,
            'duplicated_handle_batch_split_rejected':True,'capability_capturing_reusable_code_rejected':True,
            'qualification':'Checks selected ownership premises; not a full type checker.'}

if __name__=='__main__':
    result={'bounded_adaptive_equivalence':adaptive_equivalence(),'protocols':protocols(),
            'private_event_erasure':erasure(),'resources':resources(),'status':'passed',
            'qualification':'Finite exact-rational regression checks, not general proofs or a complete language implementation.'}
    print(json.dumps(result,indent=2))
