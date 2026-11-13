"""Three-world interleaved acquisition witness; not a scaling benchmark."""
import json
from dataclasses import dataclass
from exact_search import ExactSearch, Step, WIN, LOSE
from check_certificate import check_certificate

WORLDS=(((0,0),(0,0)),((0,0),(1,0)),((0,1),(0,0)))
ACTIONS=((0,0),(1,0),(0,1),(2,0),(0,2))

@dataclass(frozen=True)
class State:
    t:int
    energy:int
    previous:tuple
    done:int
    evidence:int

class PairModel:
    def __init__(self,acquisition_start=0):self.acquisition_start=acquisition_start
    def initial(self):return State(0,5,(0,0),0,7)
    def encode_state(self,s):return [s.t,s.energy,list(s.previous),s.done,s.evidence]
    def encode_action(self,a):return list(a)
    def encode_observation(self,o):return list(o)
    def terminal(self,s):
        if s.t>=4 and s.done!=3:return LOSE,'deadline_missing_stage'
        if s.done==3 and s.previous==(0,0):return WIN,'mission_complete_and_tail_cleared'
        if s.t>=5:return LOSE,'horizon_exhausted'
        return None
    def actions(self,s):
        if s.t<self.acquisition_start:return ((0,0),)
        return tuple(a for a in ACTIONS if sum(a)<=s.energy)
    def transition(self,s,a):
        outcomes={}
        for w,e in enumerate(WORLDS):
            if not (s.evidence>>w)&1:continue
            load=tuple(a[i]+sum(e[i][j]*s.previous[j] for j in range(2)) for i in range(2))
            if max(load)>3:return Step(unsafe=dict(world=w,load=list(load)))
            outcomes[load]=outcomes.get(load,0)|(1<<w)
        done=s.done
        if 2<=s.t<4:
            for i in range(2):
                if a[i]==2:done|=1<<i
        return Step(outcomes=tuple((o,State(s.t+1,s.energy-sum(a),a,done,k)) for o,k in sorted(outcomes.items())))

def main():
    report={}
    for label,start in [('early_acquisition',0),('late_acquisition',1),('no_prerelease_acquisition',2)]:
        m=PairModel(start);r=ExactSearch(m,max_nodes=100000,max_seconds=10).solve(m.initial())
        r['validation']=check_certificate(m,m.initial(),r)
        report[label]=r
    assert report['early_acquisition']['status']==WIN
    assert report['late_acquisition']['status']==LOSE
    assert report['no_prerelease_acquisition']['status']==LOSE
    with open('strict_pair_gate_results.json','w') as f:json.dump(report,f,sort_keys=True,indent=2)
    print(json.dumps({k:{'status':v['status'],'statistics':v['statistics']} for k,v in report.items()},indent=2))

if __name__=='__main__':main()
