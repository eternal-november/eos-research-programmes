#!/usr/bin/env python3
"""Constructed discovery-to-mission integration; no physical hardware claims."""
from pathlib import Path
from itertools import product
import json,math,hashlib,time
import numpy as np
from fractions import Fraction
from relational_engine import Catalogue,ForestKnowledge,iter_ids
ROOT=Path(__file__).resolve().parent

def dump(path,x):path.write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')

class Plant:
    """Hidden truth is used only here to return permitted observations and audit motion."""
    def __init__(self,cat,truth):
        self.cat=cat;self.__truth=truth
        self.c=[cat.L]*cat.n_ports # unknown initial history, never passed to learner
        self.commands=[0]*cat.n_ports
        self.observed_c=None
        self.location="calibration"
        self.energy=0
        self.transfers=[]
        self.ticks=0;self.command_energy=0;self.sensor_bits=0;self.distance=0
        self.trace=[];self.violations=[]
    def step(self,commands,cap,phase):
        allowed={'calibration':1,'aggregate':4,'individual':4,'mission':2}[self.location]
        if sum(commands)>min(cap,allowed):raise ValueError('command-access/power violation')
        self.commands=list(commands)
        self.c=[min(self.cat.L,c+1) if a else 0 for c,a in zip(self.c,commands)]
        if self.observed_c is None:
            if any(commands):raise ValueError("uninitialized observer requires all-off flush")
            self.observed_c=[0]*self.cat.n_ports
        else:
            self.observed_c=[min(self.cat.L,c+1) if a else 0 for c,a in zip(self.observed_c,commands)]
        assert self.observed_c==self.c # scorer checks observer, controller does not read hidden c
        self.ticks+=1;self.command_energy+=sum(commands);self.energy+=1+sum(commands)
        self.trace.append({'t':self.ticks,'phase':phase,'commands':list(commands),'counters':list(self.c)})
        return tuple(self.observed_c)
    def coordinate(self,i,phase):
        if phase=='calibration' and (self.location!='calibration' or sum(self.commands)>1):raise ValueError('calibration jig prohibits joint actuation')
        if phase=='individual_diagnostic' and self.location!='individual':raise ValueError('individual diagnostic sensor unavailable at this bay')
        if phase not in ('calibration','individual_diagnostic'):raise ValueError('coordinate sensor unavailable')
        y=self.cat.evaluate(self.__truth[i],self.c);self.sensor_bits+=1
        return y
    def aggregate(self,i,j):
        if self.location!="aggregate":raise ValueError("aggregate sensor unavailable at this bay")
        self.sensor_bits+=2
        return self.cat.evaluate(self.__truth[i],self.c)+self.cat.evaluate(self.__truth[j],self.c)
    def move(self,guard,fast,distance_m=10,transfer=False):
        # Exact rational quarter-second integration, including full stopping tail.
        if not transfer and self.location!="mission":raise ValueError("delivery passage unavailable at this bay")
        accel_ticks,cruise_ticks=(4,4*distance_m-3) if fast else (2,8*distance_m-2)
        velocity=Fraction(0);distance=Fraction(0);dt=Fraction(1,4)
        stage_ticks=0
        while stage_ticks<accel_ticks+cruise_ticks or velocity:
            c=self.step(self.commands,2,'fast_motion' if fast else 'slow_motion')
            high=self.cat.evaluate(self.__truth[guard],c)==1 if fast else False
            if fast and not high:self.violations.append({'t':self.ticks,'guard':guard,'type':'envelope_contract_lost'})
            if stage_ticks<accel_ticks:new=velocity+dt
            elif stage_ticks<accel_ticks+cruise_ticks:new=velocity
            else:new=max(Fraction(0),velocity-(2 if fast and high else 1)*dt)
            distance+=(velocity+new)*dt/2
            velocity=new;stage_ticks+=1
            if distance>=Fraction(distance_m)+Fraction(1,20):
                self.violations.append({'t':self.ticks,'type':'protected_boundary_collision'})
        if distance!=distance_m:self.violations.append({'type':'terminal_position_mismatch','distance':str(distance)})
        self.distance+=float(distance)
    def transfer(self,destination):
        legal={('calibration','aggregate'),('aggregate','individual'),('individual','mission')}
        if (self.location,destination) not in legal:raise ValueError('unavailable safe bay transfer')
        source=self.location;start=self.ticks
        self.commands=[0]*self.cat.n_ports
        self.move(-1,False,distance_m=1,transfer=True)
        self.location=destination
        self.transfers.append({'from':source,'to':destination,'start_tick':start,'end_tick':self.ticks,'distance_m':1})
    def truth_check(self,K):return all((K.domains[i]>>h)&1 for i,h in enumerate(self.__truth))

def update(c,a,L):return tuple(min(L,x+1) if y else 0 for x,y in zip(c,a))
def prepare(plant,features,cap=4,phase='preparation'):
    command=[0]*plant.cat.n_ports
    for p,r in features:command[p]=1
    c=tuple(plant.observed_c)
    # Explicit causal changes; no reset or simulator state overwrite.
    while any(c[p]<r for p,r in features) or tuple(plant.commands)!=tuple(command):
        c=plant.step(command,cap,phase)
    return c

def learned_features(K,i):
    descriptions=[K.catalogue.describe(h) for h in iter_ids(K.domains[i])]
    features={tuple(tuple(z) for z in d['features']) for d in descriptions}
    if len(features)!=1:raise RuntimeError('interface not identified; cannot compile')
    return [tuple(x) for x in next(iter(features))]

def live_future(cat,c,commands,steps=43):
    out=[]
    for _ in range(steps):c=update(c,commands,cat.L);out.append(c)
    return out

def coordinate_record(K,plant,i,phase):
    c=tuple(plant.observed_c);y=plant.coordinate(i,phase);K.observe_coordinate(i,c,y)
    return {'kind':'coordinate','output':i,'context':list(c),'value':y,'tick':plant.ticks,'phase':phase}

def make_case(m,seed):
    n=m+2;cat=Catalogue(n,3);rng=np.random.default_rng(seed+m)
    perm=list(map(int,rng.permutation(n)));root=int(rng.integers(2));bits=[root]
    for i in range(1,m):bits.append(1-bits[(i-1)//2])
    truth=[]
    for i in range(m):
        features=sorted([(perm[i%n],1+i%3),(perm[(i+1)%n],1+(2*i+1)%3)])
        truth.append(cat.find(features,14 if bits[i] else 6))
    return cat,truth

def run(m,seed,all_low_control=False):
    start=time.perf_counter();cat,truth=make_case(m,seed)
    if all_low_control:truth=[cat.find([],0)]*m
    plant=Plant(cat,truth)
    K=ForestKnowledge(cat,m);s=math.ceil(m/2)+1;targets=list(range(s));edges=[((i-1)//2,i) for i in range(1,s)]
    records=[]
    # A physically executed all-off tick establishes the observable run counters.
    c=plant.step([0]*cat.n_ports,1,'initial_flush')
    for i in targets:records.append(coordinate_record(K,plant,i,'calibration'))
    for p in range(cat.n_ports):
        plant.step([0]*cat.n_ports,1,'calibration_flush')
        a=[0]*cat.n_ports;a[p]=1
        for r in range(1,cat.L+1):
            plant.step(a,1,'calibration_ramp')
            for i in targets:records.append(coordinate_record(K,plant,i,'calibration'))
    # Actual protected travel to runtime diagnostic station, coarse guard only.
    plant.transfer('aggregate')
    identified=[]
    for i in targets:
        try:fs=learned_features(K,i)
        except RuntimeError:
            return {'status':'safe_abstention','reason':'task interface remains ambiguous','stopped_bay':plant.location,'ticks':plant.ticks,'violations':plant.violations}
        ds=[cat.describe(h) for h in iter_ids(K.domains[i])]
        identified.append({'output':i,'features':fs,'candidate_count':len(ds),'remaining_tables':[d['table'] for d in ds]})
    for u,v in edges:
        features=learned_features(K,u)+learned_features(K,v)
        # Union same port uses strongest required threshold.
        req={}
        for p,r in features:req[p]=max(req.get(p,0),r)
        c=prepare(plant,list(req.items()))
        c=plant.step(plant.commands,4,'aggregate_acquisition_tick')
        y=plant.aggregate(u,v);K.observe_sum(u,v,c,y)
        records.append({'kind':'aggregate','edge':[u,v],'context':list(c),'value':y,'tick':plant.ticks})
    before_individual=K.copy();rect=K.copy();rect.edges={}
    # Safe individually reachable diagnostic is not at the route fork. Pay travel.
    plant.transfer('individual')
    c=prepare(plant,learned_features(K,0),phase='individual_preparation')
    c=plant.step(plant.commands,4,'individual_acquisition_tick')
    # Verify the entire decision tree before seeing the diagnostic value.
    branch_cert=[]
    for value in K.possible_coordinate(0,c):
        branch=K.copy();branch.observe_coordinate(0,c,value)
        completion=[]
        for u,v in edges:
            options=[]
            for i in (u,v):
                fs=learned_features(branch,i);q=[0]*cat.n_ports
                for p,r in fs:q[p]=cat.L
                if branch.guarantees([(i,tuple(q),1)]):options.append(i)
            completion.append({'edge':[u,v],'certified_options':options})
        if not all(x['certified_options'] for x in completion):
            return {'status':'safe_abstention','reason':'not every possible diagnostic outcome has a certified completing continuation','stopped_bay':plant.location,'ticks':plant.ticks,'violations':plant.violations,'failed_diagnostic_branch':value}
        branch_cert.append({'diagnostic_value':value,'completion':completion})
    rec=coordinate_record(K,plant,0,'individual_diagnostic');records.append(rec)
    rect.observe_coordinate(0,tuple(plant.observed_c),rec['value'])
    plant.transfer('mission')
    commissioning=plant.ticks;commission_bits=plant.sensor_bits
    commissioning_cap=1+cat.n_ports*(cat.L+1)+30+len(edges)*(cat.L+1)+cat.L+1
    assert commissioning<=commissioning_cap
    assert plant.truth_check(K)
    rng=np.random.default_rng(seed+100*m)
    orders=[list(edges),list(reversed(edges))]+[[edges[int(j)] for j in rng.permutation(len(edges))] for _ in range(3)]
    missions=[]
    for mi,order in enumerate(orders):
        begin=plant.ticks;energy_begin=plant.energy;path=[]
        for u,v in order:
            # Choose response using learned projected world set, not truth.
            certified=[]
            for i in (u,v):
                fs=learned_features(K,i);q=[0]*cat.n_ports
                for p,r in fs:q[p]=cat.L
                if K.guarantees([(i,tuple(q),1)]):certified.append(i)
            if not certified:raise RuntimeError('compiled mission lacks safe continuation')
            chosen=min(certified);fs=learned_features(K,chosen)
            c=prepare(plant,fs,2,'mission_preparation')
            future=live_future(cat,c,plant.commands)
            assert K.guarantees([(chosen,x,1) for x in future])
            plant.move(chosen,True)
            path.append({'job':[u,v],'chosen':chosen,'finish_tick':plant.ticks,'guard_contexts':len(set(future))})
        elapsed=plant.ticks-begin;deadline=60*len(order)
        missions.append({'mission':mi,'held_out_order':mi>0,'jobs':path,'ticks':elapsed,'deadline':deadline,'energy_units':plant.energy-energy_begin,'energy_budget':3*deadline,'completed':elapsed<=deadline and plant.energy-energy_begin<=3*deadline,'elapsed_including_initialization':elapsed+(commissioning if mi==0 else 0),'deadline_including_initialization':deadline+(commissioning_cap if mi==0 else 0),'distance_m':10*len(order)})
    rect_certified=[]
    for u,v in edges:
        good=[]
        for i in (u,v):
            q=[0]*cat.n_ports
            for p,r in learned_features(rect,i):q[p]=cat.L
            if rect.guarantees([(i,tuple(q),1)]):good.append(i)
        rect_certified.append({'edge':[u,v],'options':good})
    # Supplied-scope oracle receives identical records, not extra outcomes.
    oracle=ForestKnowledge(cat,m)
    oracle_initial=[]
    for i in targets:
        actual_ports={p for p,r in cat.describe(truth[i])['features']}
        mask=0
        for h in range(cat.size):
            d=cat.describe(h)
            if {p for p,r in d['features']}==actual_ports:mask|=1<<h
        oracle.domains[i]=mask;oracle_initial.append(mask.bit_count())
    for record in records:
        if record['kind']=='coordinate':oracle.observe_coordinate(record['output'],record['context'],record['value'])
        else:oracle.observe_sum(*record['edge'],record['context'],record['value'])
    assert all(oracle.domains[i]==K.domains[i] for i in targets)
    small_reference=None
    if s<=5:
        # Central enumeration of residual global worlds, retained persistently.
        ids=[list(iter_ids(d)) for d in before_individual.domains[:s]]
        compatible=[]
        for world in product(*ids):
            okay=True
            for (u,v),e in before_individual.edges.items():
                for c,y in e.records:
                    if cat.evaluate(world[u],c)+cat.evaluate(world[v],c)!=y:okay=False;break
                if not okay:break
            if okay:compatible.append(world)
        assert len(compatible)==2
        for world in compatible:
            y=cat.evaluate(world[0],rec['context']);bc=next(b for b in branch_cert if b['diagnostic_value']==y)
            for item in bc['completion']:
                for i in item['certified_options']:
                    q=[0]*cat.n_ports
                    for p,r in learned_features(before_individual,i):q[p]=cat.L
                    assert cat.evaluate(world[i],q)==1
        small_reference={'enumerated_residual_worlds':2**s,'compatible_worlds':len(compatible),'all_branch_routes_verified':True}
    out={'status':'conditionally_certified_completion','response_count':m,'ports':cat.n_ports,'target_response_count':s,'initial_candidate_count_per_output':cat.size,
         'identified_interfaces':identified,'commissioning_ticks':commissioning,'fixed_public_commissioning_cap':commissioning_cap,'commissioning_bits':commission_bits,
         'commissioning_included_in_first_mission_deadline':True,'mission_results':missions,
         'whole_run_ticks':plant.ticks,'energy_units':plant.energy,'safe_bay_transfers':plant.transfers,'energy_budget_note':'Explicit abstract cost 1+active ports per tick; mission budget 3*deadline is nonbinding under cap2, not measured joules','command_energy_port_ticks':plant.command_energy,'distance_m':plant.distance,
         'safety_violations':plant.violations,'branch_certificate':branch_cert,
         'rectangular_same_data_certificates':rect_certified,'rectangular_full_mission_certified':all(x['options'] for x in rect_certified),
         'coarse_ticks_per_mission':82*len(edges),'coarse_later_missions_meet_deadline':82*len(edges)<=60*len(edges),'coarse_first_mission_with_same_total_time_allowance':82*len(edges)<=commissioning_cap+60*len(edges),
         'probe_all_coordinate_bits':m*(1+cat.n_ports*cat.L),'targeted_coordinate_bits':s*(1+cat.n_ports*cat.L),
         'supplied_scope_reference':{'capability':'same after identical evidence','initial_local_candidates':oracle_initial,'identical_final_target_domains':True,'acquisition_policy':'same records replayed; no claim of optimal oracle exploration','metrics':oracle.metrics()},
         'residual_joint_cartesian_worlds':str(2**s),'coherent_worlds_before_individual':2,
         'conditioning_graph_treewidth':1,'small_central_reference':small_reference,'metrics':K.metrics(),
         'seconds':time.perf_counter()-start,'trace_file':f'constructed_n{m}_trace.json'}
    dump(ROOT/f'constructed_n{m}_trace.json',{'records':records,'physical_ticks':plant.trace,'generator_truth_for_independent_audit_only':[cat.describe(h) for h in truth]})
    return out

def main():
    spec=json.loads((ROOT/'frozen_experiment.json').read_text())
    negative=run(4,spec['seed'],all_low_control=True)
    assert negative['status']=='safe_abstention' and not negative['violations']
    dump(ROOT/'safe_abstention_results.json',{'all_low_initial_class_member':negative,'scope':'Explicit safe failure outcome, not universal initial completion. All protected calibration actions and slow transfers preserve safety independently of output values.'})
    rows=[]
    for m in spec['response_counts']:
        row=run(m,spec['seed']);rows.append(row);print(m,row['seconds'],row['commissioning_ticks'],flush=True)
        dump(ROOT/'constructed_results.json',{'status':'complete' if m==spec['response_counts'][-1] else 'running','frozen_spec_sha256':hashlib.sha256((ROOT/'frozen_experiment.json').read_bytes()).hexdigest(),'runs':rows})
if __name__=='__main__':main()
