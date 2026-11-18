"""Finite direct-port count/search machines; conditional source-interface checks.

Raw words, physical keys, fault support and time are absent from private runtime
state. Logs and counters outside the machine are checker evidence, not policy.
"""
from dataclasses import dataclass
from itertools import combinations, product
from fractions import Fraction as F
from pathlib import Path
from copy import deepcopy
import argparse
import hashlib
import importlib.util
import json
import os
import subprocess
import sys

HERE = Path(__file__).resolve().parent
LEAN = Path(os.environ['USERPROFILE'])/'.elan/toolchains/leanprover--lean4---v4.33.0/bin/lean.exe'


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


class Ports:
    """External I locations. The machine receives only compare's Boolean.

    The Python local raw_word models a transient combinational operand, not a
    machine register. A physical retained/spilled operand must be mapped as I.
    The checker log stores raw values; the machine never reads that log.
    """
    def __init__(self, words, word_max=4095, physical_key=0):
        require(words and all(0 <= x <= word_max for x in words),'Invalid finite port word')
        self.words = list(words)
        self.mapping = list(range(len(words)))
        self.claimed_keys = [physical_key]*len(words)
        self.physical_keys = [physical_key]*len(words)  # Source/checker, not a returned credential.
        self.word_max = word_max
        self.log = []
        self.affected = set()  # Ghost causal footprint, not a machine input.
        self.write_attempts = 0
        self.domain_events = []

    def set_input(self, slot, word, attack=False, claimed_key=None, domain=None):
        require(0 <= slot < len(self.words) and 0 <= word <= self.word_max,'Invalid input write')
        require(claimed_key is None or 0 <= claimed_key <= self.word_max,'Metadata exceeds fixed word width')
        self.write_attempts += 1
        self.words[slot] = word
        if claimed_key is not None:
            self.claimed_keys[slot] = claimed_key
        if attack:
            self.affected.add(slot)
            self.domain_events.append((domain if domain is not None else slot,(slot,)))

    def whole_input_write(self, word):
        require(0 <= word <= self.word_max,'Invalid whole-frame word')
        self.write_attempts += len(self.words)
        self.words[:] = [word]*len(self.words)
        self.affected.update(range(len(self.words)))
        self.domain_events.append(('shared_input_writer',tuple(range(len(self.words)))))

    def shared_remap(self, physical_origin):
        require(0 <= physical_origin < len(self.words),'Invalid physical origin')
        self.mapping[:] = [physical_origin]*len(self.words)
        self.affected.update(range(len(self.words)))
        self.domain_events.append(('shared_input_mux',tuple(range(len(self.words)))))

    def compare(self, slot, operation, threshold):
        require(0 <= slot < len(self.words),'Private index escaped the physical slot range')
        require(operation in ('le','ge'),'Unknown word comparison')
        physical_origin = self.mapping[slot]
        raw_word = self.words[physical_origin]
        flag = raw_word <= threshold if operation == 'le' else raw_word >= threshold
        self.log.append({'slot':slot,'origin':physical_origin,'word':raw_word,
                         'physical_key':self.physical_keys[physical_origin],
                         'threshold':threshold,'operation':operation,'flag':flag})
        return flag


@dataclass(frozen=True)
class Parameters:
    q: int
    maximum: int
    mode: str = 'quantile'
    threshold: int = 0

    @property
    def n(self):
        return 2*self.q+1

    @property
    def pass_bound(self):
        return self.maximum.bit_length() if self.mode == 'quantile' else 1


class Machine:
    """Finite private state and an explicit read/compare/accumulate program.

    Source-private blocks have declared bounded-word costs. Input events can
    happen between every step; comparison consumes only one current port word.
    """
    def __init__(self, parameters, poison=7):
        require(parameters.q >= 0 and parameters.maximum >= 0,'Negative design parameter')
        require(parameters.mode in ('quantile','le','ge'),'Unknown program')
        require(0 <= parameters.threshold <= parameters.maximum,'Threshold outside declared domain')
        self.parameters = parameters  # Fixed design/code parameters, not incoming metadata.
        self.private_word_max = (1 << max(1,(2*max(parameters.maximum,parameters.n)+1).bit_length()))-1
        self.registers = dict.fromkeys(('lo','hi','pivot','count','index','flag','result'),
                                       min(poison,self.private_word_max))
        self.code_required_count = parameters.q+1  # A mutable instruction operand in C.
        self.initialization = (('lo',0),('hi',parameters.maximum),
                               ('pivot',parameters.threshold),('count',0),('index',0),('flag',0),('result',0))
        self.entry = 0
        self.phase = 'INIT'
        self.done = False
        self.steps = self.word_work = self.reads = self.passes = 0  # Checker work counters.
        self.execution_intact = True  # Checker only: step never consults it.
        self.private_events = []
        self.private_trace = []

    def state(self):
        return self.phase,self.entry,self.done,self.code_required_count,tuple(self.registers.items())

    def private_write(self, location, value):
        require(location in self.registers and 0 <= value <= self.private_word_max,'Invalid private write')
        changed = self.registers[location] != value
        self.registers[location] = value
        self.private_events.append((location,value,changed))
        self.execution_intact = self.execution_intact and not changed

    def code_write_required_count(self, value):
        require(0 <= value <= self.private_word_max,'Invalid code-operand write')
        changed = self.code_required_count != value
        self.code_required_count = value
        self.private_events.append(('C.required_count',value,changed))
        self.execution_intact = self.execution_intact and not changed

    def step(self, ports):
        require(not self.done,'Completed machine stepped again')
        require(len(ports.words) == self.parameters.n,'Wrong physical port group')
        r,p = self.registers,self.parameters
        self.steps += 1
        if self.phase == 'INIT':
            name,value = self.initialization[self.entry]
            r[name] = value  # One actual initialization write.
            self.entry += 1
            self.word_work += 2  # Store and instruction advance.
            if self.entry == len(self.initialization):
                self.phase = 'CHOOSE' if p.mode == 'quantile' else 'COMPARE'
                if p.mode != 'quantile':
                    self.passes = 1
        elif self.phase == 'CHOOSE':
            if r['lo'] == r['hi']:
                r['result'] = r['lo']
                self.done = True
                self.word_work += 3
            else:
                require(r['lo'] < r['hi'],'Private search bounds inverted')
                r['pivot'] = (r['lo']+r['hi'])//2
                r['count'] = r['index'] = 0
                self.phase = 'COMPARE'
                self.passes += 1
                self.word_work += 7
        elif self.phase == 'COMPARE':
            op = 'le' if p.mode == 'quantile' else p.mode
            r['flag'] = int(ports.compare(r['index'],op,r['pivot']))
            self.reads += 1
            self.phase = 'ACCUMULATE'
            self.word_work += 2  # One port comparison and control advance.
        elif self.phase == 'ACCUMULATE':
            r['count'] += r['flag']
            r['index'] += 1
            r['flag'] = 0
            self.phase = 'DECIDE' if r['index'] == p.n else 'COMPARE'
            self.word_work += 4
        elif self.phase == 'DECIDE':
            passing = r['count'] >= self.code_required_count
            if p.mode == 'quantile':
                if passing:
                    r['hi'] = r['pivot']
                else:
                    r['lo'] = r['pivot']+1
                self.phase = 'CHOOSE'
            else:
                r['result'] = int(passing)
                self.done = True
            self.word_work += 3
        else:
            raise RuntimeError('Corrupt control state has no nominal transition')
        require(all(0 <= value <= self.private_word_max for value in r.values()),'Private word overflow')
        self.private_trace.append(self.state())  # Checker trace, not machine memory.

    def budgets(self):
        z,p = len(self.initialization),self.parameters
        return {'reads':p.n*p.pass_bound,
                'word_work':2*z+(6*p.n+10)*p.pass_bound+3 if p.mode == 'quantile' else 2*z+6*p.n+3,
                'steps':z+(2*p.n+2)*p.pass_bound+1}

    def check_work(self, ports):
        budget = self.budgets()
        require(self.done and self.reads == len(ports.log),'Read accounting mismatch')
        require(self.reads <= budget['reads'] and self.word_work <= budget['word_work'],
                'Declared read/work bound exceeded')
        require(self.steps <= budget['steps'],'Finite termination bound exceeded')
        require(self.reads == self.parameters.n*self.passes,'Incomplete counted pass')
        for offset in range(0,self.reads,self.parameters.n):
            require([x['slot'] for x in ports.log[offset:offset+self.parameters.n]] == list(range(self.parameters.n)),
                    'One pass reused an apparent slot')


def execute(parameters, ports, before_step=None):
    machine = Machine(parameters)
    limit = machine.budgets()['steps']+1
    for _ in range(limit):
        if before_step:
            before_step(machine,ports)
        machine.step(ports)
        if machine.done:
            machine.check_work(ports)
            return machine
    raise RuntimeError('Finite machine did not terminate')


def static_cases():
    quantiles = permissions = max_reads = max_work = 0
    for q,maximum in ((0,7),(1,3),(2,3),(1,7)):
        for values in product(range(maximum+1),repeat=2*q+1):
            ports = Ports(values)
            machine = execute(Parameters(q,maximum),ports)
            require(machine.registers['result'] == sorted(values)[q],'Static median differs from sorting specification')
            quantiles += 1
            max_reads,max_work = max(max_reads,machine.reads),max(max_work,machine.word_work)
    for q in range(3):
        for values in product(range(4),repeat=2*q+1):
            for mode,threshold in product(('le','ge'),range(4)):
                machine = execute(Parameters(q,3,mode,threshold),Ports(values))
                expected = sum(v <= threshold if mode == 'le' else v >= threshold for v in values) >= q+1
                require(machine.registers['result'] == expected,'Permission count differs from direct specification')
                permissions += 1
    edges = []
    for q,maximum,values in ((0,0,[0]),(6,0,[4095]*6+[0]*7),
                             (1,7,[0,2,4095]),(6,2000,[4095]*6+[1000]*7)):
        machine = execute(Parameters(q,maximum),Ports(values))
        require(machine.registers['result'] == sorted(values)[q],'Endpoint/out-of-search bad word failed')
        edges.append({'q':q,'maximum':maximum,'result':machine.registers['result'],
                      'reads':machine.reads,'word_work':machine.word_work})
    return {'static_vectors':quantiles,'permission_vectors_and_thresholds':permissions,
            'maximum_static_reads':max_reads,'maximum_static_word_work':max_work,
            'singleton_and_bad_word_edges':edges}


def dynamic_reachable_cases():
    """Exhaust all reachable comparison branches, quotienting identical states.

    Endpoint words realize every possible Boolean for a nominal interval;
    0/word_max realize both adversarial answers at every search pivot.
    """
    q,maximum,lower,upper = 1,7,2,5
    n = 2*q+1
    total_states = terminals = 0
    outputs = set()
    for size in range(q+1):
        for members in combinations(range(n),size):
            affected = set(members)
            stack = [(Machine(Parameters(q,maximum)),Ports([lower]*n))]
            seen = set()
            while stack:
                machine,ports = stack.pop()
                key = machine.state(),machine.reads,machine.passes
                if key in seen:
                    continue
                seen.add(key)
                if machine.done:
                    require(lower <= machine.registers['result'] <= upper,'Changing-slot envelope violated')
                    machine.check_work(ports)
                    outputs.add(machine.registers['result'])
                    terminals += 1
                    continue
                if machine.phase == 'COMPARE':
                    i = machine.registers['index']
                    possible = (0,ports.word_max) if i in affected else (lower,upper)
                    for value in possible:
                        next_machine,next_ports = deepcopy(machine),deepcopy(ports)
                        next_ports.set_input(i,value,attack=i in affected)
                        next_machine.step(next_ports)
                        stack.append((next_machine,next_ports))
                else:
                    machine.step(ports)
                    stack.append((machine,ports))
            total_states += len(seen)
    return {'q':q,'slots':n,'range':[0,maximum],'common_envelope':[lower,upper],
            'reachable_states':total_states,'terminal_states':terminals,'outputs':sorted(outputs),
            'scope':'Complete Boolean read branching for these finite parameters; not all physical histories'}


def rotating_slot_cases():
    n,q,lower,upper = 13,6,980,1020
    results = []
    covered = set()
    for start in range(n):
        affected = {(start+k)%n for k in range(q)}
        covered |= affected
        def vary(machine,ports):
            if machine.phase == 'COMPARE':
                i = machine.registers['index']
                if i in affected:
                    value = 0 if machine.passes%2 else ports.word_max
                else:
                    value = lower if (machine.reads+i)%2 else upper
                before = machine.state()
                ports.set_input(i,value,attack=i in affected)
                require(machine.state() == before,'Input-only update changed private execution state')
        ports = Ports([1000]*n)
        machine = execute(Parameters(q,2000),ports,vary)
        require(lower <= machine.registers['result'] <= upper and machine.execution_intact,'Rotating input footprint escaped envelope')
        require(ports.affected <= affected,'Causal support exceeded declared window')
        results.append({'first_affected':start,'result':machine.registers['result'],
                        'reads':machine.reads,'word_work':machine.word_work})
    require(covered == set(range(n)),'Some slot was permanently exempted')
    return {'windows':results,'every_slot_is_faultable':True,
            'scope':'Different conditional windows, not an implemented renewal service'}


def primary_and_complementary_cases():
    auxiliary = [970]*6+[990]*6
    permission = []
    for primary in (970,990):
        ports = Ports([970]+auxiliary)
        applied = [False]
        def replace_permission_frame(machine,inputs):
            if primary != 970 and machine.phase == 'COMPARE' and not applied[0]:
                before = machine.state()
                inputs.set_input(0,primary,attack=True,claimed_key=999,domain='primary_frontend')
                require(machine.state() == before,'Primary replacement changed private execution')
                applied[0] = True
        machine = execute(Parameters(6,2000,'le',970),ports,replace_permission_frame)
        require(machine.execution_intact and ports.affected <= {0},'Primary event escaped its input footprint')
        permission.append(machine.registers['result'])
    require(permission == [1,0],'Consumed primary did not change the actual permission result')
    responses = []
    for primary in (980,1020):
        sum_ports = Ports([980]+[980]*6+[1020]*6)
        difference_ports = Ports([1000]*13)
        applied = [False]
        def replace_two_field_frame(machine,inputs):
            if primary != 980 and machine.phase == 'COMPARE' and not applied[0]:
                before = machine.state()
                inputs.set_input(0,primary,attack=True,claimed_key=999,domain='primary_frontend')
                difference_ports.set_input(0,1000,attack=True,claimed_key=999,domain='primary_frontend')
                require(machine.state() == before,'Whole primary frame replacement changed execution')
                applied[0] = True
        s = execute(Parameters(6,2000),sum_ports,replace_two_field_frame)
        d = execute(Parameters(6,2000),difference_ports)
        x = (F(s.registers['result']+d.registers['result']-1000,2),
             F(s.registers['result']-d.registers['result']+1000,2))
        command = tuple(min(F(900),max(F(300),600+2*(v-500))) for v in x)
        require(all(abs(v-500) <= 20 for v in x),'Complementary inversion escaped physical error allowance')
        responses.append({'sum':s.registers['result'],'difference_encoded':d.registers['result'],
                          'coordinates':[str(v) for v in x],'command':[str(v) for v in command],
                          'port_reads':s.reads+d.reads,'word_work_before_inversion':s.word_work+d.word_work,
                          'primary_replaced_during_job':applied[0],
                          'affected_sum_slots':sorted(sum_ports.affected),
                          'affected_difference_slots':sorted(difference_ports.affected),
                          'execution_intact':s.execution_intact and d.execution_intact})
    require(responses[0]['command'] != responses[1]['command'],'Primary row had no control consumer')
    # An ordinary permitted world / prohibited world with the same opportunity.
    low = execute(Parameters(6,2000,'le',970),Ports([600]*13))
    high = execute(Parameters(6,2000,'le',970),Ports([1200]*13))
    gap = execute(Parameters(6,1000,'ge',820),Ports([900]*13))
    require(low.registers['result'] and not high.registers['result'] and gap.registers['result'],
            'Invasive rule lost its low/high distinction')
    return {'primary_permission_results':permission,'complementary_responses':responses,
            'same_opportunity':{'low_load':600,'high_load':1200,'isolation':900,
                                'low_permitted':True,'high_permitted':False}}


def countercases():
    # Full input replacement leaves every private transition intact.
    forged = Ports([1200]*13)
    forged.whole_input_write(400)
    bad_world = execute(Parameters(6,2000,'le',970),forged)
    low_world = execute(Parameters(6,2000,'le',970),Ports([400]*13))
    require(bad_world.execution_intact and bad_world.registers['result'] == 1,'Whole-input obstruction was hidden as execution corruption')
    require(bad_world.private_trace == low_world.private_trace,'Indistinguishable private histories differ')
    require(len(forged.affected) == 13,'Whole-input domain was counted as one slot')
    unchanged = Machine(Parameters(6,2000,'le',970))
    unchanged.private_write('count',unchanged.registers['count'])
    unchanged.code_write_required_count(unchanged.code_required_count)
    require(unchanged.execution_intact,'An incident label excused execution without any private/code change')
    # One shared remapper has temporal reach to every addressed slot.
    mux = Ports([400]+[1200]*12)
    mux.shared_remap(0)
    mux_machine = execute(Parameters(6,2000,'le',970),mux)
    require(mux_machine.execution_intact and mux_machine.registers['result'] == 1,
            'Shared input-mux obstruction missing')
    require({r['origin'] for r in mux.log} == {0},'Alias fixture accidentally supplied independent origins')
    # A copied raw buffer remains an input surface even if its addresses say W.
    raw_copy_in_w = [1200]*13
    raw_copy_in_w[:] = [400]*13
    copied_permission = sum(v <= 970 for v in raw_copy_in_w) >= 7
    require(copied_permission,'Copied-record countercase missing')
    # One current input writer, moving just before each read, poisons a whole pass.
    moving = Ports([1200]*13)
    def move(machine,ports):
        if machine.phase == 'COMPARE':
            i = machine.registers['index']
            for j in range(13):
                ports.set_input(j,1200)
            ports.set_input(i,400,attack=True)
    moving_machine = execute(Parameters(6,2000,'le',970),moving,move)
    require(moving_machine.execution_intact and moving_machine.registers['result'] == 1
            and len(moving.affected) == 13,'Instantaneous-versus-window obstruction missing')
    # Real inference-state corruption is separate and remains consequential.
    private = Machine(Parameters(6,2000,'le',970))
    high = Ports([1200]*13)
    while private.phase != 'DECIDE':
        private.step(high)
    require(private.registers['count'] == 0,'Private-write fixture has an accidental input success')
    private.private_write('count',7)
    private.step(high)
    require(not private.execution_intact and private.registers['result'] == 1,
            'Private-state fault was treated as a protected correct estimator')
    code = Machine(Parameters(6,2000,'le',970))
    code.code_write_required_count(0)
    code_ports = Ports([1200]*13)
    while not code.done:
        code.step(code_ports)
    require(not code.execution_intact and code.registers['result'] == 1,
            'Startup silently repaired a corrupt code operand')
    # Physical-key truth is not recovered from a payload label or a slot count.
    wrong_key = Ports([400]*13,physical_key=1)
    wrong_key.claimed_keys[:] = [0]*13
    wrong = execute(Parameters(6,2000,'le',970),wrong_key)
    require(wrong.execution_intact and wrong.registers['result'] == 1,
            'Key-binding obstruction missing')
    # A dynamic representative need not be a median of any simultaneous snapshot.
    snapshots = []
    def switch_snapshot(machine,ports):
        if machine.phase == 'COMPARE':
            word = 3 if machine.passes == 1 else 0
            for i in range(3): ports.set_input(i,word)
            snapshots.append(word)
    dynamic = execute(Parameters(1,3),Ports([3]*3),switch_snapshot)
    require(dynamic.registers['result'] == 2 and set(snapshots) == {0,3},'Dynamic snapshot distinction lost')
    return {'whole_input_overwrite':{'actual_load':1200,'reported_load':400,'limit':1000,
                'result':bad_world.registers['result'],'execution_intact':bad_world.execution_intact,
                'affected_slots':len(forged.affected),'same_private_trace_as_low_world':True},
            'shared_input_mux':{'affected_slots':len(mux.affected),'actual_origins':[0],
                               'execution_intact':mux_machine.execution_intact,'result':mux_machine.registers['result']},
            'raw_record_copies_in_w':{'change_type':'input-only','executor_intact':True,'result':copied_permission},
            'unchanged_private_write_attempts':{'execution_intact':unchanged.execution_intact,
                                                 'actual_private_changes':0},
            'moving_writer':{'current_writers':1,'window_slots':13,'execution_intact':True,
                             'result':moving_machine.registers['result']},
            'private_count_corruption':{'changed_location':'derived count','execution_intact':False,
                                        'result':private.registers['result']},
            'code_operand_corruption':{'changed_location':'C.required_count','execution_intact':False,
                                       'result':code.registers['result'],'survives_working_state_initialization':True},
            'wrong_physical_key':{'actual_key':1,'claimed_key':0,'required_key':0,'result':wrong.registers['result']},
            'not_a_snapshot_median':{'observed_snapshot_medians':sorted(set(snapshots)),
                                     'streaming_result':dynamic.registers['result'],'common_envelope':[0,3]}}


def digest(path):
    return hashlib.sha256(path.read_bytes().replace(b'\r\n',b'\n')).hexdigest()


def check_lean(lean):
    checker_path = HERE.parent/'integration/verify.py'
    spec = importlib.util.spec_from_file_location('streaming_strict_checker',checker_path)
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    version = subprocess.run([str(lean),'--version'],capture_output=True,text=True,encoding='utf-8')
    require(version.returncode == 0 and 'version 4.33.0,' in version.stdout,'Lean4.33.0 required')
    return {'version':version.stdout.strip(),'declarations':checker.proof_check(HERE/'Streaming.lean',str(lean)),
            'checker_sha256_lf':digest(checker_path)}


def main():
    require(not sys.flags.optimize and sys.version_info[:2] == (3,12),'Unoptimized Python3.12 required')
    sys.dont_write_bytecode = True
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write',action='store_true')
    mode.add_argument('--check',action='store_true')
    parser.add_argument('--lean',type=Path,default=LEAN)
    args = parser.parse_args()
    names = ('STREAMING.md','Streaming.lean','streaming_model.py')
    before = {name:digest(HERE/name) for name in names}
    path = HERE/'streaming_results.json'
    expected = json.loads(path.read_text(encoding='utf-8')) if args.check else None
    if expected:
        require(expected['sources_sha256_lf'] == before,'Streaming sources changed; inspect before refresh')
    actual = {'schema':'local-streaming-v1','component_checks_passed':True,
              'scope':'Conditional direct-port inference; no physical isolation, renewal or source admission theorem',
              'sources_sha256_lf':before,'python_major_minor':list(sys.version_info[:2]),
              'static':static_cases(),'changing_slots':dynamic_reachable_cases(),
              'fault_rotation':rotating_slot_cases(),'primary_and_permission':primary_and_complementary_cases(),
              'countercases':countercases(),'lean':check_lean(args.lean)}
    require(before == {name:digest(HERE/name) for name in names},'Sources changed during verification')
    if args.write:
        path.write_text(json.dumps(actual,indent=2,sort_keys=True)+'\n',encoding='utf-8',newline='\n')
    else:
        require(actual == expected,'Streaming evidence differs')
    print('PASS streaming component: '+str(len(actual['lean']['declarations']))+' Lean declarations; '+
          str(actual['static']['static_vectors'])+' static vectors; '+
          str(actual['changing_slots']['reachable_states'])+' changing-slot states; source suppliers remain open')


if __name__ == '__main__':
    main()
