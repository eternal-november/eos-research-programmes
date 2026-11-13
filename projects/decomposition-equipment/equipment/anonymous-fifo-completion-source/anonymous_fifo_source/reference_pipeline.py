#!/usr/bin/env python3
"""Executable reference: anonymous bounded-delay FIFO acquisition and binding.
Public report is exactly (Fraction arrival, arbitrary binary payload). Hidden state
exists only in Plant/validate_truth; control functions have no Plant parameter.
This is a model test, not verification of the physical XOR bridge premises.
"""
from fractions import Fraction as F
from itertools import combinations
from dataclasses import dataclass
from pathlib import Path
import sys, json, random, inspect, ast
from binding_checker import check, verify_positive

class Refusal(Exception): pass
@dataclass(frozen=True)
class Caps:
    D:F; J:F; Q:F; compute:F; status:F; tail:F
    planning:F=F(7)
    initial_quiescent:bool=True
    diagnostic_isolation:bool=True
    xor_bridge:bool=True
    def validate(self):
        if self.D<=0 or self.J<0 or self.Q<=0 or min(self.compute,self.status,self.tail,self.planning)<0:
            raise Refusal('INVALID_BOUND')
        if not (self.initial_quiescent and self.diagnostic_isolation and self.xor_bridge):
            raise Refusal('MISSING_TRUSTED_CAPABILITY')

def gridceil(x,Q): return (x//Q + (x%Q != 0))*Q

class Plant:
    """Private simulator. Busy times persist; no probe/reset operation exists."""
    def __init__(self,partition,tau,J,priority):
        self.partition=tuple(partition); self.tau=tuple(tau); self.J=J
        self.priority=tuple(priority); self.busy={q:F(0) for q in partition}
        self.pending=[]; self.truth=[]; self.clock=F(0); self.counter=0
    def submit(self,requests,jitters,payloads,kind):
        # requests are (address, grid release); strict or unknown fixed tie order.
        for local,(i,t) in sorted(enumerate(requests),key=lambda z:(z[1][1],self.priority[z[1][0]])):
            assert t>=self.clock and 0<=jitters[local]<=self.J
            q=self.partition[i]; start=max(t,self.busy[q]); end=start+self.tau[i]
            self.busy[q]=end; arrival=end+jitters[local]
            record=dict(index=self.counter,address=i,release=t,start=start,end=end,
                        arrival=arrival,payload=payloads[local],kind=kind,local=local,queue=q)
            self.counter+=1; self.truth.append(record); self.pending.append(record)
    def collect(self,until):
        assert until>=self.clock
        due=sorted((r for r in self.pending if r['arrival']<=until),key=lambda r:(r['arrival'],self.priority[r['address']],r['index']))
        self.pending=[r for r in self.pending if r['arrival']>until]; self.clock=until
        return [(r['arrival'],r['payload']) for r in due]

def validate_reports(reports,count,lo,hi):
    if len(reports)!=count: raise Refusal('REPORT_COUNT')
    if any(type(r)!=tuple or len(r)!=2 or not isinstance(r[0],F) or not lo<=r[0]<=hi or r[1] not in (0,1) for r in reports):
        raise Refusal('INVALID_PUBLIC_REPORT')

def infer(ledger,n,caps):
    """ONLY public probes and trusted declared parameters; no payload identities."""
    caps.validate(); bounds={}; relations={}
    if len(ledger)!=n+n*(n-1)//2: raise Refusal('LEDGER_COUNT')
    for row in ledger:
        addresses=row['addresses']; reports=row['reports']; t=row['release']; drain=row['drain']
        validate_reports(reports,len(addresses),t,drain)
        if len(addresses)==1:
            i=addresses[0]
            if i in bounds: raise Refusal('DUPLICATE_SOLO')
            a=reports[0][0]-t; L=max(F(0),a-caps.J); U=min(caps.D,a)
            if U<=0 or L>U: raise Refusal('INCONSISTENT_SOLO')
            bounds[i]=(L,U)
        else:
            i,j=addresses
            if i not in bounds or j not in bounds or i>=j or (i,j) in relations: raise Refusal('INVALID_PAIR_LEDGER')
            Li,Ui=bounds[i]; Lj,Uj=bounds[j]; S=max(Ui,Uj)+caps.J; C=Li+Lj
            if not S<C: raise Refusal('AMBIGUOUS_PAIR_BANDS')
            m=max(r[0]-t for r in reports)
            # Reject not just gap but impossible endpoints for either class.
            same=C<=m<=Ui+Uj+caps.J
            separate=max(Li,Lj)<=m<=S
            if same==separate: raise Refusal('INCONSISTENT_PAIR')
            relations[i,j]=same
    if set(bounds)!=set(range(n)): raise Refusal('MISSING_SOLO')
    groups=[]
    for i in range(n):
        found=next((g for g in groups if relations[min(i,g[0]),max(i,g[0])]),None)
        if found is None: groups.append([i])
        else: found.append(i)
    if any(relations[i,j] != any(i in g and j in g for g in groups) for i,j in combinations(range(n),2)):
        raise Refusal('INCONSISTENT_PARTITION')
    return bounds,groups

def plan(ledger,n,caps,roles,service_release,deadline):
    """Control input boundary: public ledger + capabilities + mission contract."""
    if service_release % caps.Q: raise Refusal('OFF_GRID_SERVICE_RELEASE')
    bounds,groups=infer(ledger,n,caps)
    L=min(x[0] for x in bounds.values()); U=max(x[1] for x in bounds.values()); W=U-L
    q=len(groups); h=max(map(len,groups)); Delta=( (h*W+caps.J)//caps.Q+1)*caps.Q
    if not (Delta>h*W+caps.J and L>(q-1)*Delta+h*W+caps.J and (h-1)*caps.Q<L):
        raise Refusal('SCHEDULE_MARGIN')
    releases={i:service_release+r*Delta+k*caps.Q for r,g in enumerate(groups) for k,i in enumerate(g)}
    windows=propagate(bounds,groups,releases,caps.J)
    done=max(hi for lo,hi in windows.values())+caps.compute+caps.status+caps.tail
    if done>deadline: raise Refusal('DEADLINE')
    return dict(bounds=bounds,groups=groups,L=L,U=U,W=W,q=q,h=h,Delta=Delta,
                releases=releases,windows=windows,ready=done,roles=roles)

def propagate(bounds,groups,releases,J):
    windows={}
    for g in groups:
        low=high=F(0)
        for i in sorted(g,key=lambda i:releases[i]):
            low=max(releases[i],low)+bounds[i][0]
            high=max(releases[i],high)+bounds[i][1]
            windows[i]=(low,high+J)
    return windows

def control(plan,reports,caps,deadline,now):
    caps.validate()
    n=len(plan['roles']); validate_reports(reports,n,min(plan['releases'].values()),now)
    runtime_ready=max(now,max(t for t,b in reports))+caps.compute+caps.status+caps.tail
    edges=[[v for v,(t,b) in enumerate(reports) if plan['windows'][i][0]<=t<=plan['windows'][i][1]] for i in range(n)]
    cert=check(edges,plan['roles'],[b for t,b in reports])
    fire=cert['status']=='CERTIFIED' and verify_positive(edges,plan['roles'],[b for t,b in reports],cert) and plan['ready']<=deadline and runtime_ready<=deadline
    return dict(fire=fire,certificate=cert,edges=edges,runtime_ready=runtime_ready,deadline_met=runtime_ready<=deadline)

def commissioning_envelope(n,caps):
    """Public deterministic reservation, fixed before any probe observation."""
    t=F(0)
    for size in [1]*n+[2]*(n*(n-1)//2):
        drain=gridceil(t+size*caps.D+caps.J+caps.tail,caps.Q)
        t=gridceil(drain+caps.status+caps.compute,caps.Q)
    return t

def acquire(plant,n,caps,jitter,payload):
    """Harness transports commands/public packets; no hidden facts reach learner."""
    caps.validate(); ledger=[]; t=F(0)
    for ids in [(i,) for i in range(n)]+list(combinations(range(n),2)):
        drain=gridceil(t+len(ids)*caps.D+caps.J+caps.tail,caps.Q)
        plant.submit([(i,t) for i in ids],[jitter() for i in ids],[payload() for i in ids],'probe')
        reports=plant.collect(drain)
        ledger.append(dict(addresses=ids,release=t,drain=drain,reports=reports))
        t=gridceil(drain+caps.status+caps.compute,caps.Q)
    return ledger,t

def validate_truth(plant,p,reports,result):
    truth=[r for r in plant.truth if r['kind']=='service']
    physical={role:0 for role in p['roles']}
    for r in truth:
        physical[p['roles'][r['address']]]^=r['payload']
    # Match duplicate equal tuples by physical sorted arrival arbitration, not search.
    ordered=sorted(truth,key=lambda r:(r['arrival'],plant.priority[r['address']],r['index']))
    contained=all(v in result['edges'][r['address']] for v,r in enumerate(ordered))
    assert contained
    if result['fire']:
        cert=result['certificate']; expected=sum(physical[r]<<k for k,r in enumerate(cert['role_labels']))
        assert expected==cert['parity_mask']
    return dict(true_assignment_contained=contained,physical_role_loads=physical,
                physical_success=result['fire'],truth_only_partition=list(plant.partition),truth_only_tau=list(plant.tau))

def trial(q,h,seed):
    rng=random.Random(seed); n=q*h; J=F(1); Q=F(1); tau=F(20*q*h+20); D=tau+10
    caps=Caps(D,J,Q,F(2),F(1),F(3))
    envelope=commissioning_envelope(n,caps)
    T0=gridceil(envelope+caps.planning,Q)
    # Independently declared fixture mission contract, frozen BEFORE observations.
    deadline=T0+h*(tau+1)+(q-1)*(2*h+2)+caps.compute+caps.status+caps.tail+10
    labels=[i%q for i in range(n)]; rng.shuffle(labels)
    priority=list(range(n)); rng.shuffle(priority)
    plant=Plant(labels,[tau]*n,J,priority)
    count=0
    def jitter():
        nonlocal count
        count+=1
        return [F(0),J,F(1,2),J,F(0)][(count+seed)%5]
    # Correlated payloads deliberately do not encode addresses.
    shared=rng.randrange(2)
    def payload(): return shared
    ledger,A=acquire(plant,n,caps,jitter,payload)
    assert A<=envelope
    roles=[i%3 for i in range(n)]
    p=plan(ledger,n,caps,roles,T0,deadline)
    values=[(shared^(i//2%2)) for i in range(n)]
    plant.submit([(i,p['releases'][i]) for i in range(n)],[jitter() for i in range(n)],values,'service')
    reports=plant.collect(max(hi for lo,hi in p['windows'].values()))
    result=control(p,reports,caps,deadline,plant.clock); truth=validate_truth(plant,p,reports,result)
    assert result['fire'] and all(set(r)=={'addresses','release','drain','reports'} for r in ledger)
    serial_service=n*(D+J+caps.tail+caps.compute+caps.status)
    return dict(seed=seed,n=n,q=q,h=h,acquisition_finish=A,predeclared_commissioning_envelope=envelope,mission_contract_frozen_before_probes=True,exogenous_release=T0,deadline=deadline,
                completion_bound=p['ready'],charged_total=p['ready'],commissioning_wait=T0-A,declared_planning_allowance=caps.planning,
                acquisition_requests=n*n,postrelease_latency=p['ready']-T0,
                serial_drain_service_bound=serial_service,serial_actual_service_lower=n*tau,
                no_single_mission_overall_speed_claim=True,plan=p,public_probe_ledger=ledger,
                public_service_reports=reports,result=result,validation_private=truth), (plant,caps,ledger,p,reports)

def expect_refusal(fn):
    try: fn()
    except Refusal as e:return str(e)
    raise AssertionError('expected refusal')

def controls(context):
    import copy
    plant,caps,ledger,p,reports=context; n=len(p['roles'])
    bad=copy.deepcopy(ledger); row=bad[n]; row['reports']=[(row['release']+F(1),0)]*2
    duplicate=list(reports)+[reports[0]]
    bounds=expect_refusal(lambda:Caps(F(-1),F(0),F(1),F(0),F(0),F(0)).validate())
    pair=expect_refusal(lambda:infer(bad,n,caps))
    dup=expect_refusal(lambda:control(p,duplicate,caps,p['ready']+10,plant.clock))
    same=check([[0,1],[0,1]],['A','A'],[0,1]); cross=check([[0,1],[0,1]],['A','B'],[0,1])
    assert same['status']=='CERTIFIED' and cross['status']=='UNRESOLVED'
    # Real same-role two-queue trace: callbacks arrive reversed by jitter.
    demo=Plant([0,1],[F(5),F(5)],F(2),[0,1]); demo.submit([(0,F(0)),(1,F(1))],[F(2),F(0)],[0,1],'service')
    raw=demo.collect(F(7)); assert raw==[(F(6),1),(F(7),0)]
    demo_caps=Caps(F(5),F(2),F(1),F(0),F(0),F(0))
    demo_plan=dict(roles=['R','R'],releases={0:F(0),1:F(1)},windows={0:(F(5),F(7)),1:(F(6),F(8))},ready=F(8))
    demo_result=control(demo_plan,raw,demo_caps,F(8),demo.clock); actual=demo_result['certificate']
    validate_truth(demo,demo_plan,raw,demo_result); assert actual['status']=='CERTIFIED'
    demo_plan['roles']=['R','S']; cross_result=control(demo_plan,raw,demo_caps,F(8),demo.clock)
    validate_truth(demo,demo_plan,raw,cross_result); assert not cross_result['fire']
    # Static boundary audit: only named public arguments; runtime hidden-world
    # mutation cannot change outputs because no control function receives plant.
    names=('infer','plan','propagate','control'); signatures={name:str(inspect.signature(globals()[name])) for name in names}
    source='\n'.join(inspect.getsource(globals()[name]) for name in names)
    forbidden=('plant','tau','priority','truth','partition')
    identifiers={node.id for node in ast.walk(ast.parse(source)) if isinstance(node,ast.Name)}
    assert not identifiers.intersection(forbidden)
    fractional_caps=Caps(F(11,2),F(1,4),F(1),F(1,3),F(1,4),F(1,7))
    fractional_plant=Plant([0,1],[F(21,4),F(21,4)],F(1,4),[0,1])
    fractional_ledger,fractional_cost=acquire(fractional_plant,2,fractional_caps,lambda:F(1,4),lambda:0)
    assert all(r['release']%fractional_caps.Q==0 for r in fractional_ledger)
    assert fractional_cost%fractional_caps.Q==0
    persistent=Plant([0],[F(5)],F(0),[0]); persistent.submit([(0,F(0))],[F(0)],[0],'probe')
    persistent.submit([(0,F(1))],[F(0)],[1],'probe')
    assert [r['end'] for r in persistent.truth]==[F(5),F(10)]
    late=control(p,reports,caps,p['ready']+10,p['ready']+11)
    assert not late['fire'] and not late['deadline_met']
    missed=expect_refusal(lambda:plan(ledger,n,caps,p['roles'],min(p['releases'].values()),min(p['releases'].values())+1))
    amb=copy.deepcopy(ledger)
    wide=Caps(caps.D,caps.D,caps.Q,caps.compute,caps.status,caps.tail)
    ambiguous=expect_refusal(lambda:infer(amb,n,wide))
    before=plan(ledger,n,caps,p['roles'],min(p['releases'].values()),p['ready']+10)
    plant.tau=tuple(F(999) for _ in plant.tau); plant.partition=tuple(0 for _ in plant.partition)
    after=plan(ledger,n,caps,p['roles'],min(p['releases'].values()),p['ready']+10)
    assert before==after
    return dict(late_invocation_refuses=True,fractional_probe_bounds_grid_releases=True,fractional_probe_charged_cost=fractional_cost,persistent_busy_across_submissions=True,missed_deadline=missed,ambiguous_acquisition=ambiguous,invalid_bound=bounds,perturbed_pair=pair,duplicate_report=dup,
                same_role_ambiguity=same['status'],cross_role_ambiguity=cross['status'],
                out_of_order_raw_reports=raw,out_of_order_same_role=actual['status'],
                input_signatures=signatures,hidden_mutation_output_unchanged=True)

def encode(o):
    if isinstance(o,F): return str(o)
    raise TypeError(type(o).__name__)

def main():
    results=[]; context=None
    for q,h in [(2,2),(2,3),(3,3),(4,4)]:
        for seed in [0,1,7]:
            result,context=trial(q,h,seed); results.append(result)
    output=dict(model='anonymous FIFO one completion report; trusted physical XOR bridge',trials=results,controls=controls(context))
    try:
        from reference_baseline import robust_windows_hull, global_stagger, serial_and_drain
        base=[]
        for r in results:
            p=r['plan']; n=r['n']; spacing=(p['W']+1)//1+1
            rel={i:F(i)*spacing for i in range(n)}
            win=dict(enumerate(robust_windows_hull([p['bounds'][i] for i in range(n)],F(1),[rel[i] for i in range(n)])))
            # Strict pairwise window disjointness is a payload-independent baseline certificate.
            disjoint=all(win[i][1]<win[j][0] or win[j][1]<win[i][0] for i,j in combinations(range(n),2))
            slow=global_stagger([p['bounds'][i] for i in range(n)],F(1),F(1),spacing=p['U']+2)
            assert slow['unique_timestamp_binding']
            serial=serial_and_drain([p['bounds'][i] for i in range(n)],F(1),F(1),F(3))
            base.append(dict(slow_robust_success=slow,serial_learned_bounds=serial,seed=r['seed'],n=n,spacing=spacing,robust_unknown_partition_windows=win,
                             guaranteed_unique_binding=disjoint,latency_bound=max(w[1] for w in win.values())))
        output['global_stagger_baseline']=base
    except ImportError: output['global_stagger_baseline']='helper pending'
    target=Path(__file__).with_name('reference_pipeline_results.json'); target.write_text(json.dumps(output,default=encode,indent=2)+'\n')
    print(json.dumps(dict(trials=len(results),all_fired=all(r['result']['fire'] for r in results),controls=output['controls'],results=str(target)),default=encode,indent=2))
if __name__=='__main__': main()
