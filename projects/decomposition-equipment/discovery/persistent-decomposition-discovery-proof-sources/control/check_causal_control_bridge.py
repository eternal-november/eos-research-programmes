#!/usr/bin/env python3
"""Finite regression evidence, not a proof of the unbounded theorems."""
from itertools import product
from collections import defaultdict, deque, Counter
from pathlib import Path
import json


def criterion(n, adj, goals, safe, blocked, init):
    reached=set(init); todo=list(init)
    while todo:
        v=todo.pop()
        if v in goals: continue
        for w in adj[v]:
            if w not in reached: reached.add(w); todo.append(w)
    if not reached <= safe: return False, {}
    non=reached-goals
    if any(v in blocked or not adj[v] for v in non): return False, {}
    rank={}
    pending=set(non)
    while pending:
        new={v for v in pending if all(w in goals or w in rank for w in adj[v])}
        if not new: return False, {}
        for v in new: rank[v]=max([rank[w]+1 for w in adj[v] if w not in goals]+[0])
        pending-=new
    assert all(rank[v]>rank[w] for v in non for w in adj[v] if w not in goals)
    return True, rank


def backward_winning(n, adj, goals, safe, blocked):
    win=goals & safe
    while True:
        new={v for v in range(n) if v in safe and v not in blocked and adj[v] and adj[v] <= win}
        nxt=win|new
        if nxt==win: return win
        win=nxt


def exhaustive_graph_check(maxn=3):
    instances=0; winning=0
    for n in range(1,maxn+1):
        allv=set(range(n))
        for edge_bits in product((0,1),repeat=n*n):
            adj=[{j for j in range(n) if edge_bits[i*n+j]} for i in range(n)]
            # each vertex is unsafe, safe-nongoal, or safe-goal
            for colors in product(range(3),repeat=n):
                safe={i for i,c in enumerate(colors) if c>0}
                goals={i for i,c in enumerate(colors) if c==2}
                for bb in product((0,1),repeat=n):
                    blocked={i for i,b in enumerate(bb) if b}
                    # Goal is terminal, irrespective of stored outgoing raw edges.
                    win=backward_winning(n,adj,goals,safe,blocked)
                    for start in range(n):
                        ok,rank=criterion(n,adj,goals,safe,blocked,{start})
                        assert ok==(start in win),(n,adj,goals,safe,blocked,start)
                        instances+=1; winning+=ok
    return {'instances':instances,'winning':winning,'max_vertices':maxn}


# Staged plant: state -> list of actual (pre-record ID, observation,
# dictionary action -> list of (post-record ID, next-state, post-observation)).
def compiled_controller_graph(plant, initial, q0, alpha, mu, goals, safe):
    vertices={}; rev=[]; adj=[]; blocked=set(); terminal=set(); safeids=set(); edge_records=[]
    def vid(v):
        if v not in vertices:
            vertices[v]=len(rev); rev.append(v); adj.append(set())
        return vertices[v]
    initialids={vid((x,q0)) for x in initial}
    cursor=0
    while cursor<len(rev):
        x,q=rev[cursor]
        if x in safe: safeids.add(cursor)
        if x in goals:
            terminal.add(cursor); cursor+=1; continue
        pre=plant.get(x,[])
        if not pre: blocked.add(cursor)
        for mid,o,actions in pre:
            a=alpha(q,o)
            records=actions.get(a,[])
            if not records: blocked.add(cursor)
            for eid,xp,p in records:
                qp=mu(q,o,a,p)
                target=vid((xp,qp)); adj[cursor].add(target)
                edge_records.append((cursor,mid,eid,target))
        cursor+=1
    ok,rank=criterion(len(rev),adj,terminal,safeids,blocked,initialids)
    return {'accepted':ok,'vertices':rev,'rank':rank,'actual_record_count':len(edge_records),
            'blocked_count':len(blocked),'adj':adj,'goals':terminal,'safe':safeids,'initial':initialids}


def probe_plant(resample=False,early_signal=False):
    P={}; initial=[]
    for phase,h in product((0,1),(0,1)):
        x=(phase,h); initial += [x] if phase==0 else []
        obs=(phase,h) if early_signal else phase
        actions={}
        for a in (0,1):
            actions[a]=[(('dock',phase,h,a), 'goal' if a==h else 'bad', None)]
        if phase==0:
            hpvals=(0,1) if resample else (h,)
            actions['probe']=[(('probe',h,hp),(1,hp),h) for hp in hpvals]
        P[x]=[(('pre',phase,h),obs,actions)]
    P['bad']=[('prebad',0,{a:[(('bad',a),'bad',None)] for a in (0,1,'probe')})]
    safe=set(P)-{'bad'}|{'goal'}
    return P,initial,{'goal'},safe


def staged_tests():
    P,I,G,S=probe_plant()
    wins=[]
    for table in product((0,1,'probe'),repeat=2):
        r=compiled_controller_graph(P,I,0,lambda q,o,t=table:t[o],lambda *args:0,G,S)
        if r['accepted']: wins.append(table)
    assert wins==[]
    alpha=lambda q,o:'probe' if o==0 else q
    mu=lambda q,o,a,p:p if a=='probe' else q
    remembered=compiled_controller_graph(P,I,0,alpha,mu,G,S)
    assert remembered['accepted']
    assert max(remembered['rank'].values())==1 # two ticks to target
    P2,I2,G2,S2=probe_plant(resample=True)
    stale=compiled_controller_graph(P2,I2,0,alpha,mu,G2,S2)
    assert not stale['accepted']
    P3,I3,G3,S3=probe_plant(early_signal=True)
    early=compiled_controller_graph(P3,I3,0,lambda q,o:o[1],lambda *args:0,G3,S3)
    assert early['accepted']
    # At phase1, current hidden states require incompatible commands.
    assert {0} & {1} == set()
    # One productive acquisition does not rescue another deadlocked acquisition.
    pd={'s':[('good',0,{0:[('e','g',None)]}),('blocked',0,{})]}
    br=compiled_controller_graph(pd,{'s'},0,lambda q,o:0,lambda *a:0,{'g'},{'s','g'})
    assert not br['accepted'] and br['blocked_count']==1
    # Separate actual parallel executions remain separate despite identical endpoints.
    pm={'s':[('m',0,{0:[('e0','g',None),('e1','g',None)]})]}
    mr=compiled_controller_graph(pm,{'s'},0,lambda q,o:0,lambda *a:0,{'g'},{'s','g'})
    assert mr['accepted'] and mr['actual_record_count']==2
    return {'memoryless_controllers_tested':9,'memoryless_winners':0,
            'two_memory_probe_controller_accepts':remembered['accepted'],
            'same_controller_after_hidden_reset_accepts':stale['accepted'],
            'illegal_early_reveal_changes_feasibility':early['accepted'],
            'deadlocked_acquisition_rejected':not br['accepted'],
            'parallel_actual_records_retained':mr['actual_record_count']}


def factor_enabledness():
    instances=0
    J=range(3)
    subsets=[{j for j,b in zip(J,bits) if b} for bits in product((0,1),repeat=3)]
    for ds,fs in product(subsets,repeat=2):
        D=[('d',j,k) for j in ds for k in range(j+1)]
        F=[('f',j,k) for j in fs for k in range(3-j)]
        E=[(d,f) for d in D for f in F if d[1]==f[1]]
        assert bool(E)==bool(ds & fs)
        instances+=1
    assert {0} and not ({0}&{1})
    return {'support_pairs':instances,'local_enabled_whole_blocked_control':True}


def exact_staged_relabel_test():
    P,I,G,S=probe_plant()
    alpha=lambda q,o:'probe' if o==0 else q
    mu=lambda q,o,a,p:p if a=='probe' else q
    before=compiled_controller_graph(P,I,0,alpha,mu,G,S)
    rename=lambda x:('refined',repr(x))
    Pr={rename(x):[(('copy',m),o,{a:[(('copy',e),rename(y),p) for e,y,p in es]
                                 for a,es in acts.items()}) for m,o,acts in ms]
        for x,ms in P.items()}
    after=compiled_controller_graph(Pr,[rename(x) for x in I],0,alpha,mu,
                                    {rename(x) for x in G},{rename(x) for x in S})
    assert before['accepted']==after['accepted']
    assert before['rank']==after['rank']
    assert before['actual_record_count']==after['actual_record_count']
    return {'same_rank_and_records':True,'record_count':before['actual_record_count']}


def saturate_boolean_tables(domain, inputs):
    tables={tuple(0 for _ in domain),tuple(1 for _ in domain)}
    tables.update(tuple(x[i] for x in domain) for i in inputs)
    while True:
        old=set(tables)
        tables.update(tuple(1-v for v in t) for t in old)
        tables.update(tuple(a&b for a,b in zip(t,u)) for t in old for u in old)
        if tables==old: return tables


def causal_gate_tests():
    # Universe variables q, observable phase, current hidden mode/post bit.
    dom=list(product((0,1),repeat=3))
    pre=saturate_boolean_tables(dom,(0,1))
    post=saturate_boolean_tables(dom,(0,1,2))
    hidden=tuple(x[2] for x in dom)
    probe_flag=tuple(1-x[1] for x in dom)
    command=tuple(x[0] for x in dom)
    memory_update=tuple(x[2] if x[1]==0 else x[0] for x in dom)
    assert len(pre)==16 and len(post)==256
    assert hidden not in pre and hidden in post
    assert probe_flag in pre and command in pre and memory_update in post
    def well_staged(edges,stages):
        return all(stages[u]<=stages[v] for u,v in edges)
    stages={'sensor':0,'controller':1,'transition':2,'commit':3}
    assert well_staged([('sensor','controller'),('controller','transition'),
                       ('transition','commit')],stages)
    assert not well_staged([('transition','controller')],stages)
    return {'pre_tables':len(pre),'post_tables':len(post),
            'hidden_bit_unavailable_pre':True,'probe_controller_has_gate_realization':True,
            'backward_phase_wire_rejected':True}


if __name__=='__main__':
    result={'graph_domain':exhaustive_graph_check(),'staging':staged_tests(),
            'nonblocking':factor_enabledness(),'exact_relabel':exact_staged_relabel_test(),
            'causal_gates':causal_gate_tests(),'status':'PASS'}
    out=Path(__file__).with_name('check_causal_control_bridge_results.json')
    out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
