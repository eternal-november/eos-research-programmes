"""Option-preserving diagnosis is distinct from pure completion/classification.

Supplementary finite semantic gate, not a scaling experiment or novelty claim.
Initial oracle-feasibility predicate is fixed: L,R feasible; broken infeasible.
"""
from dataclasses import dataclass
import json
from exact_search import ExactSearch,Step,WIN,LOSE
from check_certificate import check_certificate

@dataclass(frozen=True)
class DState:
    energy:int
    worlds:int
    completed:bool=False

class DiagnosisModel:
    def __init__(self,energy,objective):self.energy=energy;self.objective=objective
    def initial(self):return DState(self.energy,7)
    def encode_state(self,s):return [s.energy,s.worlds,s.completed]
    def encode_action(self,a):return a
    def encode_observation(self,o):return o
    def terminal(self,s):
        if self.objective=='classify' and not(s.worlds&(s.worlds-1)):
            return WIN,'feasibility_class_identified'
        if s.completed:return WIN,'service_completed'
        if s.worlds==4:
            return (WIN,'certified_initially_infeasible') if self.objective=='diagnose_and_serve' else (LOSE,'broken_world_cannot_complete')
        if s.energy==0:return LOSE,'remaining_service_option_exhausted'
        return None
    def actions(self,s):return tuple(a for a,c in [('probe',2),('serve_L',1),('serve_R',1)] if c<=s.energy)
    def transition(self,s,a):
        if a=='probe':return Step(outcomes=tuple((i,DState(s.energy-2,1<<i)) for i in range(3) if s.worlds>>i&1))
        intended=0 if a=='serve_L' else 1;wrong=1-intended
        if s.worlds>>wrong&1:return Step(unsafe={'world':wrong,'reason':'wrong_service_mode'})
        out=[]
        if s.worlds>>intended&1:out.append(('done',DState(s.energy-1,1<<intended,True)))
        if s.worlds&4:out.append(('broken',DState(s.energy-1,4)))
        return Step(outcomes=tuple(out))

def main():
    results=[]
    for objective,energy,expected in [('complete',3,LOSE),('diagnose_and_serve',3,WIN),('diagnose_and_serve',2,LOSE),('classify',2,WIN)]:
        m=DiagnosisModel(energy,objective);r=ExactSearch(m).solve(m.initial())
        assert r['status']==expected
        r['validation']=check_certificate(m,m.initial(),r);r['objective']=objective;r['energy']=energy
        results.append(r)
    json.dump({'scope':'Supplementary semantic gate only','initial_oracle_feasibility':{'L':True,'R':True,'broken':False},'results':results},open('diagnosis_gate_results.json','w'),indent=2,sort_keys=True)
    print([(r['objective'],r['energy'],r['status']) for r in results])
if __name__=='__main__':main()
