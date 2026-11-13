#!/usr/bin/env python3
"""Dense independent replay of every sequential policy branch; no author engine imports."""
from pathlib import Path
from fractions import Fraction
import sys,json,hashlib
import numpy as np
from independent_execution_check import catalogue,val,advance
ROOT=Path(__file__).resolve().parents[1];EX=ROOT/'example';cat=catalogue(4);N=len(cat);cache={}
def pred(c):
 c=tuple(c)
 if c not in cache:cache[c]=np.array([val(h,c) for h in cat],dtype=np.int8)
 return cache[c]
def project(mats,ds=None):
 ds=[np.ones(N,dtype=bool) for _ in range(4)] if ds is None else [d.copy() for d in ds]
 while True:
  changed=False
  for (u,v),a in mats.items():
   x=ds[u]&np.any(a[:,ds[v]],axis=1);y=ds[v]&np.any(a[x,:],axis=0)
   changed|=not np.array_equal(x,ds[u]) or not np.array_equal(y,ds[v]);ds[u]=x;ds[v]=y
  if not changed:return ds

def verify(cfg,order,mats,ds,c,t,e,policy,leg=0):
 if leg==len(order):
  assert policy['terminal']=='all deliveries completed';assert t==policy['elapsed_ticks'] and e==policy['energy_used'];assert t<=cfg['absolute_deadline_ticks'] and e<=cfg['absolute_energy_budget'];return 1
 assert policy['leg']==leg and policy['edge']==order[leg] and policy['diagnostic_output']==order[leg][0]
 a=policy['command'];prep=policy['prep_ticks'];assert a in cfg['held_patterns'] and prep in cfg['prep_lengths'];assert policy['diagnostic_ticks']==cfg['diagnostic_ticks']
 for _ in range(prep+cfg['diagnostic_ticks']):c=advance(c,a);t+=1;e+=sum(a)
 assert list(c)==policy['counter_context_at_diagnostic'] and t==policy['elapsed_ticks_at_diagnostic'] and e==policy['energy_at_diagnostic']
 u=order[leg][0];p=pred(c);outcomes=[b for b in (0,1) if np.any(ds[u]&(p==b))];assert sorted(b['coordinate_outcome'] for b in policy['branches'])==outcomes
 leaves=0
 for branch in policy['branches']:
  dd=[d.copy() for d in ds];dd[u]&=p==branch['coordinate_outcome'];dd=project(mats,dd);assert all(np.any(d) for d in dd)
  selected=branch['selected_endpoint'];assert selected in order[leg];distance=10 if selected%2==0 else 12;travel=4*distance+3
  assert branch['distance_m']==distance and branch['passage_ticks']==travel
  cc=c;v=Fraction(0);d=Fraction(0)
  for tick in range(travel):
   cc=advance(cc,a);assert np.all(pred(cc)[dd[selected]]==1)
   vn=v+Fraction(1,4) if tick<4 else v if tick<travel-2 else max(0,v-Fraction(1,2));d+=(v+vn)/8;v=vn;assert d<Fraction(distance)+Fraction(1,20)
  assert v==0 and d==distance
  tt=t+travel;ee=e+sum(a)*travel+distance
  assert branch['elapsed_ticks_after_passage']==tt and branch['energy_after_passage']==ee and branch['counter_context_after_passage']==list(cc)
  leaves+=verify(cfg,order,mats,dd,cc,tt,ee,branch['next'],leg+1)
 return leaves

def exists(cfg,order,mats,ds,c,t,e,leg=0):
 # Exhaust the same finite option grammar independently using dense relations.
 if leg==len(order):return t<=cfg['absolute_deadline_ticks'] and e<=cfg['absolute_energy_budget']
 if t+sum(min(43 if i%2==0 else 51 for i in edge)+min(cfg['prep_lengths'])+cfg['diagnostic_ticks'] for edge in order[leg:])>cfg['absolute_deadline_ticks']:return False
 for prep in cfg['prep_lengths']:
  for a in cfg['held_patterns']:
   dc=c;dt=prep+cfg['diagnostic_ticks'];t1=t+dt;e1=e+sum(a)*dt
   for _ in range(dt):dc=advance(dc,a)
   p=pred(dc);u=order[leg][0];possible=[b for b in (0,1) if np.any(ds[u]&(p==b))];allgood=bool(possible)
   for b in possible:
    dd=[d.copy() for d in ds];dd[u]&=p==b;dd=project(mats,dd);good=False
    for i in sorted(order[leg],key=lambda x:(x%2,x)):
     distance=10 if i%2==0 else 12;travel=4*distance+3;tt=t1+travel;ee=e1+sum(a)*travel+distance
     if tt>cfg['absolute_deadline_ticks'] or ee>cfg['absolute_energy_budget']:continue
     cc=dc;safe=True
     for _ in range(travel):
      cc=advance(cc,a)
      if not np.all(pred(cc)[dd[i]]==1):safe=False;break
     if safe and exists(cfg,order,mats,dd,cc,tt,ee,leg+1):good=True;break
    if not good:allgood=False;break
   if allgood:return True
 return False

def main(path):
 data=json.loads(path.read_text());cfg=data['config'];total=0;positive=0
 for root in data['results']:
  mats={x:np.ones((N,N),dtype=bool) for x in [(0,1),(1,2),(2,3)]};c=(3,)*4;t=e=0
  for _ in range(cfg['initial_flush_ticks']):c=advance(c,[0]*4);t+=1
  for r in root['base_records']:
   c=advance(c,r['command']);t+=1;e+=sum(r['command']);assert r['tick']==t and r['counters']==list(c)
   edge=tuple(r['edge']);assert r['sum']==sum(val(root['truth_generator_scoring_only'][i],c) for i in edge);p=pred(c);mats[edge]&=p[:,None]+p[None,:]==r['sum']
  for _ in range(cfg['initial_transfer_ticks']):c=advance(c,cfg['initial_transfer_command']);t+=1;e+=sum(cfg['initial_transfer_command'])
  e+=cfg['initial_transfer_energy'];assert t==root['paid_initial_ticks'] and e==root['paid_initial_energy'] and list(c)==root['initial_counter_context'];ds=project(mats)
  for label,out in root['outcomes'].items():
   independent=exists(cfg,root['mission_order'],mats if label=='exact' else {},ds,c,t,e)
   assert independent==out['certified'],(root['seed'],root['order_index'],label)
   if not out['certified']:continue
   positive+=1;leaves=verify(cfg,root['mission_order'],mats if label=='exact' else {},ds,c,t,e,out['policy']);assert leaves==out['certificate_replay']['leaves'];total+=leaves
 result={'input':path.name,'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'roots':len(data['results']),'independently_verified_positive_policies':positive,'independently_verified_universal_leaves':total,'negative_solver_results':'all independently exhausted with dense-CSP finite-grammar search; every certification decision matched','physical_scope':'rational passage integration checked; initial transfer abstract unless config states independent physical contract; no hardware validation'}
 target=ROOT/'review'/('independent_'+path.stem+'_check.json');target.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main(Path(sys.argv[1]) if len(sys.argv)>1 else EX/'sequential_mission_results.json')
