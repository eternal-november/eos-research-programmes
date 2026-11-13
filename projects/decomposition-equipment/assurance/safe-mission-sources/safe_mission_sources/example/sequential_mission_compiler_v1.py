#!/usr/bin/env python3
"""Frozen small sequential AND-OR mission compiler; abstract motion contracts.

No truth access occurs in Solver. Scalar truth is used only to reconstruct the
fixed acquisition observations and to replay the resulting actual branch.
"""
from __future__ import annotations
from pathlib import Path
import hashlib,itertools,json,random,time
from relational_engine import Catalogue,ForestKnowledge
from partial_acquisition_probe import advance,plant_bit,essential_tables,interface_summary

ROOT=Path(__file__).resolve().parent

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def motion(c,command,ticks,L):
    contexts=[]
    for _ in range(ticks):
        c=advance(c,command,L);contexts.append(c)
    return c,list(dict.fromkeys(contexts))

def distance(endpoint):return 10 if endpoint%2==0 else 12

def duration(endpoint):return 4*distance(endpoint)+3


class Solver:
    def __init__(self,cfg,order):
        self.cfg,self.order=cfg,order
        self.memo={};self.guard_cache={}
        self.counts={'visited_states':0,'state_cache_hits':0,'candidate_preparations':0,
                     'coordinate_outcome_branches':0,'endpoint_tail_checks':0,
                     'guard_cache_hits':0,'resource_prunes':0,
                     'checker_propagation_calls':0,'checker_arc_revisions':0,
                     'checker_signature_checks':0,'checker_feasibility_queries':0,
                     'maximum_recursive_depth':0}

    def counted(self,k,method,*args):
        before=dict(k.counters);out=getattr(k,method)(*args)
        for name in ('propagation_calls','arc_revisions','signature_checks','feasibility_queries'):
            self.counts['checker_'+name]+=k.counters[name]-before[name]
        return out

    def guard(self,k,endpoint,contexts):
        key=(k.state_key(),endpoint,tuple(contexts))
        if key in self.guard_cache:
            self.counts['guard_cache_hits']+=1;return self.guard_cache[key]
        self.counts['endpoint_tail_checks']+=1
        good=self.counted(k,'guarantees',[(endpoint,c,1) for c in contexts])
        self.guard_cache[key]=good;return good

    def search(self,k,c,leg,ticks,energy):
        self.counts['maximum_recursive_depth']=max(self.counts['maximum_recursive_depth'],leg)
        if leg==len(self.order):
            return {'terminal':'all deliveries completed','elapsed_ticks':ticks,'energy_used':energy}
        key=(leg,c,ticks,energy,k.state_key())
        if key in self.memo:
            self.counts['state_cache_hits']+=1;return self.memo[key]
        self.counts['visited_states']+=1
        # Optimistic suffix resource lower bound; it cannot discard a valid tree.
        min_ticks=sum(min(duration(u) for u in edge)+min(self.cfg['prep_lengths'])+self.cfg['diagnostic_ticks']
                      for edge in self.order[leg:])
        min_energy=sum(min(distance(u) for u in edge) for edge in self.order[leg:])
        if ticks+min_ticks>self.cfg['absolute_deadline_ticks'] or energy+min_energy>self.cfg['absolute_energy_budget']:
            self.counts['resource_prunes']+=1;self.memo[key]=None;return None
        edge=self.order[leg]
        for prep in self.cfg['prep_lengths']:
            for command_raw in self.cfg['held_patterns']:
                command=tuple(command_raw);self.counts['candidate_preparations']+=1
                diag_ticks=prep+self.cfg['diagnostic_ticks']
                dc,_=motion(c,command,diag_ticks,self.cfg['L'])
                t1=ticks+diag_ticks;e1=energy+sum(command)*diag_ticks
                if t1>self.cfg['absolute_deadline_ticks'] or e1>self.cfg['absolute_energy_budget']:
                    self.counts['resource_prunes']+=1;continue
                outcomes=self.counted(k,'possible_coordinate',edge[0],dc)
                branches=[];works=bool(outcomes)
                for bit in outcomes:
                    self.counts['coordinate_outcome_branches']+=1
                    branch=k.copy()
                    assert self.counted(branch,'observe_coordinate',edge[0],dc,bit)
                    chosen=None
                    for endpoint in sorted(edge,key=lambda u:(duration(u),u)):
                        travel=duration(endpoint);t2=t1+travel;e2=e1+sum(command)*travel+distance(endpoint)
                        if t2>self.cfg['absolute_deadline_ticks'] or e2>self.cfg['absolute_energy_budget']:
                            self.counts['resource_prunes']+=1;continue
                        final,contexts=motion(dc,command,travel,self.cfg['L'])
                        if not self.guard(branch,endpoint,contexts):continue
                        suffix=self.search(branch,final,leg+1,t2,e2)
                        if suffix is not None:
                            chosen={'coordinate_outcome':bit,'selected_endpoint':endpoint,
                                    'distance_m':distance(endpoint),'passage_ticks':travel,
                                    'counter_context_after_passage':list(final),
                                    'elapsed_ticks_after_passage':t2,'energy_after_passage':e2,
                                    'next':suffix}
                            break
                    if chosen is None:
                        works=False;break
                    branches.append(chosen)
                if works:
                    policy={'leg':leg,'edge':list(edge),'command':list(command),'prep_ticks':prep,
                            'diagnostic_ticks':self.cfg['diagnostic_ticks'],
                            'diagnostic_output':edge[0],'counter_context_at_diagnostic':list(dc),
                            'elapsed_ticks_at_diagnostic':t1,'energy_at_diagnostic':e1,
                            'branches':branches}
                    self.memo[key]=policy;return policy
        self.memo[key]=None;return None


def verify_policy(cfg,order,k,c,leg,ticks,energy,policy):
    """Independent recursive all-branch resource and guard certificate replay."""
    if leg==len(order):
        assert policy.get('terminal')=='all deliveries completed'
        assert ticks==policy['elapsed_ticks'] and energy==policy['energy_used']
        assert ticks<=cfg['absolute_deadline_ticks'] and energy<=cfg['absolute_energy_budget']
        return {'leaves':1,'max_ticks':ticks,'max_energy':energy,'nodes':0}
    assert policy['leg']==leg and policy['edge']==list(order[leg])
    cmd=tuple(policy['command']);assert list(cmd) in cfg['held_patterns']
    prep=policy['prep_ticks'];assert prep in cfg['prep_lengths']
    assert policy['diagnostic_ticks']==cfg['diagnostic_ticks']
    dc=c
    for _ in range(prep+cfg['diagnostic_ticks']):dc=advance(dc,cmd,cfg['L'])
    t1=ticks+prep+cfg['diagnostic_ticks'];e1=energy+sum(cmd)*(prep+cfg['diagnostic_ticks'])
    assert list(dc)==policy['counter_context_at_diagnostic']
    assert t1==policy['elapsed_ticks_at_diagnostic'] and e1==policy['energy_at_diagnostic']
    endpoint0=order[leg][0]
    possible=k.possible_coordinate(endpoint0,dc)
    assert sorted(b['coordinate_outcome'] for b in policy['branches'])==list(possible)
    out={'leaves':0,'max_ticks':0,'max_energy':0,'nodes':1}
    for b in policy['branches']:
        bk=k.copy();assert bk.observe_coordinate(endpoint0,dc,b['coordinate_outcome'])
        u=b['selected_endpoint'];assert u in order[leg]
        travel=4*distance(u)+3
        assert b['distance_m']==distance(u) and b['passage_ticks']==travel
        cc=dc;all_contexts=[]
        for _ in range(travel):
            cc=advance(cc,cmd,cfg['L']);all_contexts.append(cc)
        # Deliberately verify every tick, not the compiler's unique-context compression.
        assert bk.guarantees([(u,q,1) for q in all_contexts])
        t2=t1+travel;e2=e1+sum(cmd)*travel+distance(u)
        assert list(cc)==b['counter_context_after_passage']
        assert t2==b['elapsed_ticks_after_passage'] and e2==b['energy_after_passage']
        suffix=verify_policy(cfg,order,bk,cc,leg+1,t2,e2,b['next'])
        out['leaves']+=suffix['leaves'];out['nodes']+=suffix['nodes']
        out['max_ticks']=max(out['max_ticks'],suffix['max_ticks']);out['max_energy']=max(out['max_energy'],suffix['max_energy'])
    return out


def actual_replay(cfg,truth,c,ticks,energy,policy):
    trace=[];distance_total=0
    while 'terminal' not in policy:
        cmd=tuple(policy['command'])
        for _ in range(policy['prep_ticks']+cfg['diagnostic_ticks']):
            c=advance(c,cmd,cfg['L']);ticks+=1;energy+=sum(cmd)
        bit=plant_bit(truth[policy['diagnostic_output']],c)
        b=next(x for x in policy['branches'] if x['coordinate_outcome']==bit)
        u=b['selected_endpoint'];guard=[]
        for _ in range(b['passage_ticks']):
            c=advance(c,cmd,cfg['L']);ticks+=1;energy+=sum(cmd)
            guard.append(plant_bit(truth[u],c))
        assert all(v==1 for v in guard)
        energy+=distance(u);distance_total+=distance(u)
        trace.append({'leg':policy['leg'],'diagnostic_bit':bit,'selected_endpoint':u,
                      'all_passage_tick_guards_high':True,'elapsed_ticks':ticks,'energy':energy,
                      'counter_context_after':list(c)})
        policy=b['next']
    assert ticks<=cfg['absolute_deadline_ticks'] and energy<=cfg['absolute_energy_budget']
    return {'completed_legs':len(trace),'distance_m':distance_total,'elapsed_ticks':ticks,
            'energy_used':energy,'trace':trace,'violations':0}


def main():
    cfg=json.loads((ROOT/'sequential_mission_config.json').read_text())
    acquisition=json.loads((ROOT/'partial_acquisition_config.json').read_text())
    assert sha(ROOT/'partial_acquisition_config.json')==cfg['source_acquisition_config_sha256']
    cat=Catalogue(cfg['n_ports'],cfg['L']);results=[];started=time.perf_counter()
    summary={'roots':0,'exact_certified':0,'rectangular_certified':0,'exact_only':0,
             'both_uncertified':0,'verified_policy_leaves':0,'actual_replay_violations':0}
    for seed in cfg['truth_seeds']:
        rng=random.Random(seed);truth=[]
        for i in range(cfg['n_outputs']):
            ports=sorted(rng.sample(range(cfg['n_ports']),2))
            truth.append({'features':[[p,rng.randint(2,cfg['L'])] for p in ports],
                          'table':rng.choice(essential_tables())})
        k=ForestKnowledge(cat,cfg['n_outputs']);c=(cfg['L'],)*cfg['n_ports'];ticks=0;energy=0;records=[]
        for _ in range(cfg['initial_flush_ticks']):c=advance(c,(0,)*cfg['n_ports'],cfg['L']);ticks+=1
        for t,cmd in enumerate(acquisition['initial_command_vectors']):
            c=advance(c,cmd,cfg['L']);ticks+=1;energy+=sum(cmd)
            edge=acquisition['edges'][t%len(acquisition['edges'])]
            total=sum(plant_bit(truth[u],c) for u in edge)
            assert k.observe_sum(*edge,c,total)
            records.append({'tick':ticks,'command':cmd,'counters':list(c),'edge':edge,'sum':total})
        for _ in range(cfg['initial_transfer_ticks']):
            c=advance(c,cfg['initial_transfer_command'],cfg['L']);ticks+=1
            energy+=sum(cfg['initial_transfer_command'])
        energy+=cfg['initial_transfer_energy']
        true_ids=[cat.find(m['features'],m['table']) for m in truth]
        assert k.feasible(domain_restrictions={i:1<<h for i,h in enumerate(true_ids)})
        for order_idx,order in enumerate(cfg['mission_orders']):
            exact=k.copy();rect=ForestKnowledge(cat,cfg['n_outputs']);rect.domains=list(exact.domains)
            outputs={}
            for label,root in [('exact',exact),('rectangular',rect)]:
                solver=Solver(cfg,order);before=dict(cat.counters);t0=time.perf_counter()
                policy=solver.search(root,c,0,ticks,energy)
                elapsed=time.perf_counter()-t0
                result={'certified':policy is not None,'elapsed_seconds':elapsed,
                        'search_counts':solver.counts,'memoized_states':len(solver.memo),
                        'guard_cache_entries':len(solver.guard_cache),
                        'catalogue_operation_delta':{name:cat.counters[name]-before[name] for name in before}}
                if policy is not None:
                    certificate=verify_policy(cfg,order,root,c,0,ticks,energy,policy)
                    replay=actual_replay(cfg,truth,c,ticks,energy,policy)
                    result.update(policy=policy,certificate_replay=certificate,actual_replay=replay)
                    summary['verified_policy_leaves']+=certificate['leaves']
                    summary['actual_replay_violations']+=replay['violations']
                outputs[label]=result
            a,b=outputs['exact']['certified'],outputs['rectangular']['certified']
            # Both searches are complete over the same finite option grammar.
            assert not b or a
            summary['roots']+=1;summary['exact_certified']+=a;summary['rectangular_certified']+=b
            summary['exact_only']+=a and not b;summary['both_uncertified']+=not a and not b
            results.append({'seed':seed,'order_index':order_idx,'mission_order':order,
                            'truth_generator_scoring_only':truth,'base_records':records,
                            'paid_initial_ticks':ticks,'paid_initial_energy':energy,
                            'initial_counter_context':list(c),
                            'root_interfaces':{str(i):interface_summary(k,i) for i in range(cfg['n_outputs'])},
                            'root_knowledge_metrics':k.metrics(),'outcomes':outputs})
            print(json.dumps({'seed':seed,'order':order_idx,'exact':a,'rectangular':b,
                              'exact_states':outputs['exact']['search_counts']['visited_states'],
                              'rectangle_states':outputs['rectangular']['search_counts']['visited_states']}),flush=True)
    output={'config_sha256':sha(ROOT/'sequential_mission_config.json'),
            'source_sha256':sha(__file__),'engine_sha256':sha(ROOT/'relational_engine.py'),
            'summary':summary,'elapsed_seconds':time.perf_counter()-started,
            'scope':'Abstract timed option certificate under deterministic response and initial safe acquisition premises; no physical access/hardware validation. Conditional on actually acquired root evidence; no universal initial-world completion guarantee.',
            'config':cfg,'results':results}
    (ROOT/'sequential_mission_results.json').write_text(json.dumps(output,indent=2)+'\n')
    (ROOT/'sequential_mission_summary.json').write_text(json.dumps({key:value for key,value in output.items() if key not in ('results','config')},indent=2)+'\n')
    print(json.dumps(summary,indent=2),flush=True)


if __name__=='__main__':main()
