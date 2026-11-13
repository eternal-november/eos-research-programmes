"""Adversarial budget-control tests of author solver with independent models."""
import sys,pathlib,time,json,hashlib
ROOT=pathlib.Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'example'))
from exact_search import ExactSearch,Step
class Branching:
    def __init__(self,delay_actions=0,delay_transition=0):self.calls=0;self.delay_actions=delay_actions;self.delay_transition=delay_transition
    def encode_state(self,s):return s
    def encode_action(self,a):return a
    def encode_observation(self,o):return o
    def terminal(self,s):return ('WIN','done') if s>=10 else None
    def actions(self,s):time.sleep(self.delay_actions);return tuple(range(1000))
    def transition(self,s,a):self.calls+=1;time.sleep(self.delay_transition);return Step(outcomes=((a,s+1),))
results=[]
for label,nodes,seconds,da,dt,maxcalls in [('node_one',1,10,0,0,1),('node_zero',0,10,0,0,0),('slow_actions',100,0.005,0.025,0,0),('slow_transition',100,0.005,0,0.025,1),('many_siblings',2,10,0,0,2)]:
    m=Branching(da,dt);solver=ExactSearch(m,nodes,seconds);r=solver.solve(0)
    assert r['status']=='UNKNOWN' and not r['certificate'] and not solver.active
    assert m.calls<=maxcalls and r['statistics']['expanded']<=nodes
    results.append(dict(test=label,calls=m.calls,expanded=r['statistics']['expanded'],elapsed=r['statistics']['elapsed_seconds'],status=r['status']))
report=dict(status='PASS',tests=results,solver_sha256=hashlib.sha256((ROOT/'example'/'exact_search.py').read_bytes()).hexdigest(),qualification='Global exhaustion stops sibling search; wall budget is soft and cannot interrupt one model call. Certificate extraction/serialization/checking is outside this search cap. Terminal/memo handling occurs before the generic visit cap; no generic hard real-time guarantee.')
(ROOT/'review'/'independent_cap_results.json').write_text(json.dumps(report,sort_keys=True,indent=2));print(json.dumps(report,indent=2))
