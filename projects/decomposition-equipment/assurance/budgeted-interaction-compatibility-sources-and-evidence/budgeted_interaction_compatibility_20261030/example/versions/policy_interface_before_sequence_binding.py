"""Supplemental interpreter for already checked policy certificates.

This is a concrete API discipline, not a linear type system, a Markov-category
implementation, or a safety guarantee after the model assumptions fail. Copying
report values is allowed; copying a live runtime handle is explicitly refused.
The host still owns exactly-once physical actuation and faithful measurement.
"""
from dataclasses import dataclass
from copy import deepcopy
from check_certificate import check_certificate
from exact_search import WIN

class ProtocolError(RuntimeError): pass
class ContractViolation(RuntimeError): pass

def freeze(x):
    if isinstance(x,list):return tuple(freeze(y) for y in x)
    if isinstance(x,dict):return tuple(sorted((k,freeze(v)) for k,v in x.items()))
    return x

@dataclass(frozen=True)
class Observation:
    values:tuple
    def __post_init__(self):
        if type(self.values) is not tuple or any(type(x) is not int for x in self.values):
            raise TypeError('Observation must be a tuple of exact integer readouts')

@dataclass(frozen=True)
class Command:
    controls:tuple
    credits:tuple
    sequence:int

@dataclass(frozen=True)
class Instruction:
    state:tuple
    terminal:bool
    action:tuple|None
    outcomes:tuple

class PolicyInterface:
    def __init__(self,model,initial,result):
        if result['status']!=WIN:raise ValueError('Only a certified WIN is executable')
        checked=check_certificate(model,initial,result)
        assert checked['status']=='PASS'
        raw=deepcopy(result['certificate'])
        self._program={}
        for key,rec in raw.items():
            terminal=rec['kind']=='terminal'
            if terminal:
                assert rec['status']==WIN
                instruction=Instruction(freeze(rec['state']),True,None,())
            else:
                assert rec['kind']=='choice'
                instruction=Instruction(freeze(rec['state']),False,freeze(rec['action']),
                    tuple((tuple(e['observation']),e['next']) for e in rec['outcomes']))
            self._program[key]=instruction
        self._node=result['root'];self._awaiting=False;self._rejected=False;self._sequence=0
        self.certificate_root=result['root']
    def __copy__(self):raise TypeError('A live runtime handle cannot be copied')
    def __deepcopy__(self,memo):raise TypeError('A live runtime handle cannot be copied')
    @property
    def state(self):return self._program[self._node].state
    @property
    def phase(self):
        if self._rejected:return 'REJECTED'
        if self._awaiting:return 'AWAITING_OBSERVATION'
        if self._program[self._node].terminal:return 'DONE'
        return 'READY'
    def issue(self):
        if self.phase!='READY':raise ProtocolError('No new command is currently authorized')
        controls,credits=self._program[self._node].action
        command=Command(controls,credits,self._sequence)
        self._awaiting=True
        return command
    def observe(self,report):
        if self.phase!='AWAITING_OBSERVATION':raise ProtocolError('No issued command awaits a report')
        if not isinstance(report,Observation):raise TypeError('Expected immutable Observation value')
        destinations=dict(self._program[self._node].outcomes)
        if report.values not in destinations:
            self._rejected=True
            raise ContractViolation('Readout is outside this checked continuation contract')
        self._node=destinations[report.values];self._awaiting=False;self._sequence+=1
        return self.state
