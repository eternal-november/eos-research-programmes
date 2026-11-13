#!/usr/bin/env python3
"""Independent concrete state-machine checks for the three-coupling example.

The controller sees dummy readout and public receipts, never the hidden latch.
The concrete simulator independently stores the latch and useful-work tokens.
These finite checks do not establish the unbounded protocol theorem.
"""
from dataclasses import dataclass, field
import argparse
import copy
import functools
import itertools
import json
from pathlib import Path


def require(ok, why):
    if not ok:
        raise RuntimeError(why)


class IllegalAction(Exception):
    pass


class TerminalTrace(Exception):
    pass


@dataclass
class Plant:
    theta: tuple
    hold_until: int = 11
    deadline: int = 10
    time: int = 0
    mode: str = 'Idle'
    latch: int = 0
    activity: tuple = (0, 0, 0)
    required: set = field(default_factory=set)
    done: set = field(default_factory=set)
    trace: list = field(default_factory=list)
    target: int = 0
    owner: bool = True
    evidence: object = None
    epoch: int = 0
    available: set = field(default_factory=lambda: {'A', 'B'})

    def tick(self, action):
        if self.time + 1 > self.hold_until:
            raise IllegalAction('holding interval exhausted')
        self.time += 1
        self.trace.append((self.time, action))

    def load_dummy(self):
        if self.mode != 'Idle' or not self.owner:
            raise IllegalAction('dummy load state/ownership')
        self.tick('load_dummy')
        self.mode, self.latch, self.activity = 'Dummy', 0, (0, 0, 0)

    def dummy_pulse(self, j):
        if self.mode != 'Dummy' or not self.owner:
            raise IllegalAction('dummy pulse state/ownership')
        self.tick('dummy_' + 'ABC'[j])
        self.latch ^= self.theta[j]
        self.activity = tuple(b ^ int(i == j) for i, b in enumerate(self.activity))

    def read_dummy(self):
        if self.mode != 'Dummy' or not self.owner:
            raise IllegalAction('dummy read state')
        self.tick('read_dummy')
        self.mode = 'DummyRead'
        if self.activity == (1, 1, 0):
            self.evidence = (self.epoch, self.latch)
        return self.latch

    def drain(self):
        if self.mode != 'DummyRead' or not self.owner:
            raise IllegalAction('drain state')
        self.tick('drain_dummy')
        self.mode = 'Idle'
        self.latch, self.activity = 0, (0, 0, 0)

    def load_product(self, target):
        if self.mode != 'Idle' or not self.owner:
            raise IllegalAction('production load state/ownership')
        self.tick('load_product')
        self.mode, self.latch, self.target = 'Pending', target, target
        self.activity, self.required, self.done = (0, 0, 0), {'A', 'B'}, set()

    def work(self, j):
        name = 'ABC'[j]
        if self.mode != 'Pending' or not self.owner or name not in self.required or name not in self.available:
            raise IllegalAction('work requires pending ownership and an unspent work token')
        self.tick('work_' + name)
        self.required.remove(name)
        self.done.add(name)
        self.latch ^= self.theta[j]
        self.activity = tuple(b ^ int(i == j) for i, b in enumerate(self.activity))

    def seal(self, evidence_bit, certificate_current=True):
        if self.mode != 'Pending' or self.required or not self.owner:
            raise IllegalAction('seal before useful work/ownership complete')
        if (not certificate_current or self.activity != (1, 1, 0)
                or self.evidence != (self.epoch, evidence_bit)):
            raise IllegalAction('no current pair certificate')
        if self.time + 2 > min(self.hold_until, self.deadline):
            raise IllegalAction('seal must reserve commit time')
        # Supplied correction actuator performs a known toggle; its availability
        # is not inferred from the learner's proof. Even zero correction costs1.
        self.tick('seal_' + str(evidence_bit))
        self.latch ^= evidence_bit
        self.mode = 'Sealed'

    def commit(self):
        if (self.mode != 'Sealed' or not self.owner
                or self.evidence is None or self.evidence[0] != self.epoch
                or self.time + 1 > self.deadline):
            raise IllegalAction('commit requires sealed owner')
        self.tick('commit')
        output = self.latch
        self.mode = 'Complete'
        return output

    def wait(self):
        if self.mode != 'Pending':
            raise IllegalAction('wait state')
        self.tick('wait')

    def withdraw(self):
        self.evidence = None
        if self.mode == 'Sealed':
            self.mode = 'Invalidated'

    def abort(self):
        if self.mode not in ('Pending', 'Sealed', 'Invalidated') or not self.owner:
            raise IllegalAction('abort state/ownership')
        self.tick('safe_abort')
        self.mode = 'Aborted'
        # Actual useful work remains done and tokens remain spent. Abort removes
        # the connector safely; it is not an inverse of work or a successful job.


def charge_rejection(method):
    @functools.wraps(method)
    def call(self, *args, **kwargs):
        if self.mode in ('Expired', 'Complete', 'Aborted'):
            raise TerminalTrace('modeled attempt has ended; no continuation or safety claim')
        try:
            return method(self, *args, **kwargs)
        except IllegalAction:
            self.time += 1
            self.trace.append((self.time, 'reject_' + method.__name__))
            if self.time > self.hold_until:
                self.mode = 'Expired'
            # Expired has no certified physical safety guarantee.
            raise
    return call


for method_name in ('load_dummy', 'dummy_pulse', 'read_dummy', 'drain',
                    'load_product', 'work', 'seal', 'commit', 'wait', 'abort'):
    setattr(Plant, method_name, charge_rejection(getattr(Plant, method_name)))


def rejected(thunk, description):
    # Negative controls branch from a saved state, not from the successful run.
    # Otherwise each deliberate rejection would spend its genuine clock tick.
    plant = getattr(thunk, '__self__', None)
    if plant is None:
        plant = next((cell.cell_contents for cell in (thunk.__closure__ or ())
                      if isinstance(cell.cell_contents, Plant)), None)
    require(isinstance(plant, Plant), 'negative control lacks explicit plant')
    before = copy.deepcopy(plant.__dict__)
    try:
        thunk()
    except IllegalAction:
        expected = before['time'] + 1
        require(plant.time == expected, 'rejection time not charged: ' + description)
        for key in before:
            if key == 'mode' and expected > before['hold_until']:
                require(plant.mode == 'Expired', 'missing expiry state')
            elif key not in ('time', 'trace'):
                require(plant.__dict__[key] == before[key], 'rejection mutated ' + key)
        plant.__dict__.clear()
        plant.__dict__.update(before)
        return
    raise RuntimeError('illegal action accepted: ' + description)


def commission(p, order=(0, 1)):
    p.load_dummy()
    for j in order:
        p.dummy_pulse(j)
    measured = p.read_dummy()
    p.drain()
    require(p.mode == 'Idle' and p.time == 5, 'commissioning not fully charged/drained')
    return measured


def check_traces():
    worlds = list(itertools.product((0, 1), repeat=3))
    positive = []
    interrupted = []
    wrong_command_failures = 0
    for theta, target, probe_order, work_order in itertools.product(
            worlds, (0, 1), ((0, 1), (1, 0)), ((0, 1), (1, 0))):
        p = Plant(theta)
        y = commission(p, probe_order)
        # Controller command depends only on this actual readout/public activity.
        p.load_product(target)
        rejected(p.read_dummy, 'live production readout')
        rejected(p.drain, 'live production reset/drain')
        rejected(p.load_dummy, 'dummy load over live connector')
        rejected(lambda: p.load_product(target), 'absolute target reset while pending')
        for j in work_order:
            p.work(j)
        require(p.done == {'A', 'B'} and not p.required, 'useful work omitted')
        p.seal(y)
        rejected(lambda: p.work(0), 'work after sealing')
        output = p.commit()
        require(output == target and p.time == 10, 'positive mission failed')
        positive.append(dict(theta=list(theta), target=target, probe_order=list(probe_order),
                             work_order=list(work_order), evidence=y, final_time=p.time,
                             route=output, trace=p.trace))
        # Same completed work but a wrong correction must not be accepted as a
        # purported interchangeable implementation.
        if (target ^ theta[0] ^ theta[1]) != target:
            wrong_command_failures += 1
    for theta, target, first, delay in itertools.product(worlds, (0, 1), (0, 1), range(3)):
        p = Plant(theta)
        y = commission(p)
        p.load_product(target)
        p.work(first)
        require(p.time == 7 and len(p.required) == 1, 'bad interruption point')
        rejected(lambda: p.seal(y), 'seal at ambiguous incomplete prefix')
        rejected(lambda: p.commit(), 'commit at unsealed prefix')
        rejected(lambda: p.work(first), 'repeat spent work as free undo')
        for _ in range(delay):
            p.wait()
        decision_time = p.time
        if p.time + 3 <= 10:
            p.work(1 - first)
            p.seal(y)
            require(p.commit() == target, 'permitted completion repair failed')
            outcome = 'COMPLETED'
        elif p.time + 1 <= p.hold_until:
            already_done = set(p.done)
            p.abort()
            require(p.done == already_done and len(p.required) == 1,
                    'abort restored work tokens or undid work')
            outcome = 'SAFE_ABORT_MISSION_FAILED'
        else:
            outcome = 'NO_HOLD_CERTIFICATE'
        interrupted.append(dict(theta=list(theta), target=target, first=first,
                                delay=delay, decision_time=decision_time,
                                outcome=outcome, final_time=p.time))
    # Exhausted holding time must NOT be described as automatically safe to abort.
    late = Plant((0, 0, 0))
    commission(late)
    late.load_product(0)
    late.work(0)
    for _ in range(4):
        late.wait()
    rejected(late.abort, 'abort tail beyond holding guarantee')
    # A sealed withdrawal invalidates Commit; only paid safe disposal remains.
    withdrawn = Plant((0, 1, 0))
    bit = commission(withdrawn)
    withdrawn.load_product(0)
    withdrawn.work(0)
    withdrawn.work(1)
    withdrawn.seal(bit)
    rejected(withdrawn.wait, 'client delay inside protected sealed tail')
    withdrawn.withdraw()
    rejected(withdrawn.commit, 'commit after sealed evidence withdrawal')
    withdrawn.abort()
    require(withdrawn.time == 10 and withdrawn.mode == 'Aborted', 'withdrawal abort cost')
    # Absolute mission deadline is distinct from the one-tick disposal tail.
    tail = Plant((0, 0, 0))
    commission(tail)
    tail.load_product(0)
    tail.work(0)
    for _ in range(3):
        tail.wait()
    tail.abort()
    require(tail.time == 11 and tail.mode == 'Aborted', 'protected disposal tail')
    # Fault injection outside the alphabet demonstrates why the sealed lease matters.
    corrupt = Plant((0, 1, 0))
    y = commission(corrupt)
    corrupt.load_product(0)
    corrupt.work(0)
    corrupt.work(1)
    corrupt.seal(y)
    corrupt.latch ^= corrupt.theta[1]  # unauthorized B effect, not an admitted call
    require(corrupt.commit() == 1, 'missing-lease counterexample absent')
    # Expiry ends the modeled trace; stored saturation is not stopped physical time.
    expired = Plant((0, 0, 0), time=11, mode='Pending')
    try:
        expired.abort()
    except IllegalAction:
        pass
    require(expired.mode == 'Expired' and expired.time == 12, 'expiry transition')
    snapshot = copy.deepcopy(expired.__dict__)
    for _ in range(3):
        try:
            expired.abort()
        except TerminalTrace:
            pass
        else:
            raise RuntimeError('terminal continuation accepted')
        require(expired.__dict__ == snapshot, 'terminal API continued modeled clock')
    # Ownership is supplied authority, not created by a data/evidence certificate.
    no_owner = Plant((0, 0, 0), owner=False)
    rejected(no_owner.load_dummy, 'proof without ownership')
    # Two worlds agree on every isolated zero-activity load/read experiment but
    # disagree after the required coupled activity.
    isolated_pair = ((0, 0, 0), (1, 0, 0))
    isolated_outputs = []
    coupled_outputs = []
    for t in isolated_pair:
        iso = Plant(t)
        iso.load_dummy()
        isolated_outputs.append(iso.read_dummy())
        iso.drain()
        mixed = Plant(t)
        mixed.load_dummy()
        mixed.dummy_pulse(0)
        mixed.dummy_pulse(1)
        coupled_outputs.append(mixed.read_dummy())
        mixed.drain()
    require(isolated_outputs == [0, 0], 'isolated control')
    require(coupled_outputs == [0, 1], 'coupling did not distinguish physical outputs')
    require({t[0] ^ t[1] for t in isolated_pair} == {0, 1}, 'coupled distinction absent')
    # Forged evidence, withdrawn evidence, and changed epochs do not authorize sealing.
    for problem in ('forged', 'withdrawn', 'epoch', 'late'):
        p = Plant((1, 0, 0))
        y = commission(p)
        p.load_product(0)
        p.work(0)
        p.work(1)
        supplied = y
        if problem == 'forged':
            supplied ^= 1
        elif problem == 'withdrawn':
            p.evidence = None
        elif problem == 'epoch':
            p.epoch += 1  # fault injection, not an admitted reconfiguration action
        else:
            p.wait()
        rejected(lambda: p.seal(supplied), problem + ' seal')
    unavailable = Plant((1, 0, 0))
    commission(unavailable)
    unavailable.load_product(0)
    unavailable.work(0)
    unavailable.available.remove('B')
    rejected(lambda: unavailable.work(1), 'unavailable remaining work')
    unavailable.abort()
    require(unavailable.done == {'A'} and unavailable.required == {'B'},
            'unavailable work silently counted complete')
    # After pair-calibration, individual prefix is still ambiguous.
    q0_worlds = [t for t in worlds if t[0] ^ t[1] == 0]
    require(len(q0_worlds) == 4 and {t[2] for t in q0_worlds} == {0, 1},
            'partial identification accidentally complete')
    require({t[0] for t in q0_worlds} == {0, 1}, 'prefix ambiguity lost')
    return dict(status='PASS', assumptions='Stationary linear couplings; trusted owner, closed gate, calibration readout, correction actuator and one-tick operations; mission deadline10; hold through11; rejection1 tick on forked negative-control branches.',
                positive_trace_count=len(positive), interrupted_trace_count=len(interrupted),
                failed_uncorrected_trace_count=wrong_command_failures,
                positive_traces=positive, interrupted_traces=interrupted,
                partial_identification_worlds_for_readout0=[list(t) for t in q0_worlds],
                late_abort='REJECTED_AFTER_H11', sealed_withdrawal='ABORT_ONLY', missing_lease_fault='WRONG_ROUTE', expiry_terminal='NO_MODELED_CONTINUATION', protected_tail_abort_time=11, unsupported_ownership='REJECTED',
                forged_withdrawn_epoch_late_seals='REJECTED',
                unavailable_remaining_job='SAFE_ABORT_MISSION_FAILED',
                isolated_outputs=isolated_outputs, coupled_outputs=coupled_outputs)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = check_traces()
    rendered = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.output:
        args.output.write_text(rendered)
    print(json.dumps({k: v for k, v in result.items() if k not in ('positive_traces', 'interrupted_traces')},
                     indent=2, sort_keys=True))

if __name__ == '__main__':
    main()
