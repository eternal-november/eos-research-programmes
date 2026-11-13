"""Actual wrapper exercised against independent dense physical semantics.

Imports wrapper API and Step carrier, but no author ladder model, simulator,
workload generator or policy planner. Constructor validation receives an adapter
backed by the independent reference interpreter.
"""
import sys,pathlib,json,gzip,copy,hashlib
from independent_execution_audit import Reference,freeze
ROOT=pathlib.Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'example'))
from policy_interface import PolicyInterface,Observation,ProtocolError,ContractViolation
from exact_search import Step
path=ROOT/'example/results/n4_s731_p2_r1_e0_certificate.json.gz'
result=json.loads(gzip.decompress(path.read_bytes()));case=result['case'];ref=Reference(case['n'],result['jobs'],case['power'],case['energy'])
class Adapter:
    def initial(self):return ref.initial()
    def encode_state(self,s):return json.loads(json.dumps(s))
    def encode_action(self,a):return json.loads(json.dumps(a))
    def encode_observation(self,o):return list(o)
    def actions(self,s):return ref.actions(s)
    def terminal(self,s):return ref.terminal(s)
    def transition(self,s,a):
        step=ref.step(s,a)
        return Step(unsafe={'supported':True}) if step.get('unsafe') else Step(outcomes=tuple(step['outcomes']))
adapter=Adapter();counts=dict(worlds=0,ticks=0,stale_round_rejections=0,immediate_duplicate_rejections=0,duplicate_issue_rejections=0)
for world in ref.worlds:
    runtime=PolicyInterface(adapter,ref.initial(),result);s=ref.initial();prior=None
    while runtime.phase!='DONE':
        assert runtime.state==s
        command=runtime.issue();a=(command.controls,command.credits);assert a in ref.actions(s)
        assert command.sequence==s[0]
        try:runtime.issue();raise AssertionError('duplicate issue accepted')
        except ProtocolError:counts['duplicate_issue_rejections']+=1
        if prior is not None:
            before=(runtime.state,runtime.phase)
            try:runtime.observe(prior);raise AssertionError('stale round accepted')
            except ProtocolError:counts['stale_round_rejections']+=1
            assert before==(runtime.state,runtime.phase)
        loads=tuple(a[0][i]+(0 if p<0 else s[2][p]) for i,p in enumerate(world))
        assert max(loads)<=3
        sn=dict(ref.step(s,a)['outcomes'])[loads]
        report=Observation(loads,command.sequence);dupe=copy.copy(report)
        assert dupe.values==report.values and dupe.sequence==report.sequence
        got=runtime.observe(report);assert got==sn
        try:runtime.observe(dupe);raise AssertionError('immediate duplicate accepted')
        except ProtocolError:counts['immediate_duplicate_rejections']+=1
        s=sn;prior=report;counts['ticks']+=1
    assert ref.terminal(s)==('WIN','mission_complete_and_tail_cleared');counts['worlds']+=1
# A mutable caller-owned certificate cannot rewrite the constructed program.
mut=copy.deepcopy(result);runtime=PolicyInterface(adapter,ref.initial(),mut)
original=freeze(mut['certificate'][mut['root']]['action']);mut['certificate'][mut['root']]['action'][0][0]=99
command=runtime.issue();assert (command.controls,command.credits)==original
# Current-round impossible report permanently rejects the runtime.
bad=PolicyInterface(adapter,ref.initial(),result);command=bad.issue()
try:bad.observe(Observation((99,)*case['n'],command.sequence));raise AssertionError('impossible report accepted')
except ContractViolation:pass
assert bad.phase=='REJECTED'
for operation in [bad.issue,lambda:bad.observe(Observation((0,)*case['n'],command.sequence))]:
    try:operation();raise AssertionError('operation after rejection accepted')
    except ProtocolError:pass
for maker in [lambda:Observation((True,),0),lambda:Observation((0,),True),lambda:Observation((0,),-1),lambda:Observation([0],0)]:
    try:maker();raise AssertionError('invalid observation type accepted')
    except TypeError:pass
for copier in [copy.copy,copy.deepcopy]:
    try:copier(runtime);raise AssertionError('copy API accepted runtime')
    except TypeError:pass
report=dict(status='PASS',counts=counts,caller_mutation_isolated=True,current_round_impossible_report_permanent_rejection=True,exact_integer_observation_types=True,copy_api_rejects_live_handle=True,qualifications=['Sequence binds protocol rounds but is not authentication; a host can fabricate current-sequence plausible values.','Host must enact each command once and supply faithful corresponding measurements.','API copy rejection is not a linear type/capability system or a guarantee against arbitrary Python mutation.','Rejecting after a violated premise does not itself establish physical recovery or safety.'],hashes={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [ROOT/'example/policy_interface.py',ROOT/'example/POLICY_INTERFACE_SUPPLEMENT_MANIFEST.json',path]})
(ROOT/'review/independent_policy_interface_results.json').write_text(json.dumps(report,sort_keys=True,indent=2));print(json.dumps(report,indent=2))
