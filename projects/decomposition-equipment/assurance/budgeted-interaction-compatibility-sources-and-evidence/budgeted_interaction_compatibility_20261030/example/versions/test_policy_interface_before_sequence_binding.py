"""Post-protocol regression; does not change or rerun measured decisions."""
import copy,gzip,json,hashlib,datetime
from dataclasses import FrozenInstanceError
from ladder_model import LadderModel,Job
from policy_interface import PolicyInterface,Observation,ProtocolError,ContractViolation

def main():
    path='results/n4_s731_p2_r1_e0_certificate.json.gz'
    with gzip.open(path,'rt') as f:result=json.load(f)
    case=result['case'];jobs=tuple(Job(j['release'],j['deadline'],tuple(map(tuple,j['routes']))) for j in result['jobs'])
    model=LadderModel(case['n'],jobs,case['power'],case['energy'])
    outcomes=[];physical_ticks=0
    for world in model.inf.complete_worlds(model.inf.initial()):
        runtime=PolicyInterface(model,model.initial(),result)
        prev=(0,)*model.n;steps=0
        while runtime.phase!='DONE':
            command=runtime.issue()
            try:runtime.issue();raise AssertionError('duplicate issue accepted')
            except ProtocolError:pass
            load=tuple(command.controls[i]+(0 if world[i]<0 else prev[world[i]]) for i in range(model.n))
            assert max(load)<=3
            report=Observation(load);duplicate=copy.copy(report)
            assert duplicate.values==report.values
            runtime.observe(report)
            try:runtime.observe(duplicate);raise AssertionError('duplicate observation consumed')
            except ProtocolError:pass
            prev=command.controls;steps+=1
        assert not any(prev)
        outcomes.append({'world':world,'steps':steps,'final_state':runtime.state});physical_ticks+=steps
    bad=PolicyInterface(model,model.initial(),result);bad.issue()
    try:bad.observe(Observation((99,)*model.n));raise AssertionError('bad report accepted')
    except ContractViolation:pass
    assert bad.phase=='REJECTED'
    try:bad.issue();raise AssertionError('issued after rejection')
    except ProtocolError:pass
    live=PolicyInterface(model,model.initial(),result)
    for copier in (copy.copy,copy.deepcopy):
        try:copier(live);raise AssertionError('copied live handle')
        except TypeError:pass
    immutable=Observation((0,)*model.n)
    try:immutable.values=(1,);raise AssertionError('report mutated')
    except FrozenInstanceError:pass
    summary=dict(status='PASS',worlds=len(outcomes),physical_ticks=physical_ticks,
                 duplicate_issue_rejected=True,duplicate_observation_rejected=True,
                 invalid_report_permanently_rejects=True,live_handle_copy_rejected=True,
                 immutable_report_copy_allowed=True,
                 caveat='Rejection is not a guarantee of safety after assumptions fail; host owns exactly-once actuation.',
                 source_certificate_sha256=hashlib.sha256(open(path,'rb').read()).hexdigest(),
                 per_world=outcomes)
    json.dump(summary,open('policy_interface_results.json','w'),indent=2,sort_keys=True)
    manifest=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
        scope='Post-protocol executable-interface wrapper and regression; no measured planner, protocol, source, or decision changes.',
        files={p:hashlib.sha256(open(p,'rb').read()).hexdigest() for p in ['policy_interface.py','test_policy_interface.py','policy_interface_results.json']})
    json.dump(manifest,open('POLICY_INTERFACE_SUPPLEMENT_MANIFEST.json','w'),indent=2,sort_keys=True)
    print({k:v for k,v in summary.items() if k!='per_world'})
if __name__=='__main__':main()
