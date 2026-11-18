"""Exact-rational delayed-cutoff clamp traces; no clean image or close-started oracle.

The simulated mechanical trajectory is linear between integer event times.
The proof in CLAMP.md quantifies over all signals satisfying its raw bounds;
the finite trajectories here are adversarial checks, not that universal proof.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
import json
import math
import os
from pathlib import Path
import re
import subprocess
import sys

if sys.flags.optimize:
    raise RuntimeError('Unoptimized Python is required')

HERE = Path(__file__).resolve().parent
LEAN = Path(os.environ['USERPROFILE']) / '.elan/toolchains/leanprover--lean4---v4.33.0/bin/lean.exe'


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def dz(value, threshold):
    return value-threshold if value > threshold else value+threshold if value < -threshold else F(0)


@dataclass(frozen=True)
class Command:
    force: F = F(0)
    write: tuple[int, int] | None = None


@dataclass
class Producer:
    reference: tuple[int, ...]
    force: F = F(2)
    cursor: int = 0
    ready: bool = False
    joined: bool = False

    def invoke(self, measured, error, age_loss, marker, cell, guard='robust'):
        # Only measured finite-word position and an ordinary own-cell read enter.
        # Real q, sample time, hostile identities and the intended image do not.
        if not self.ready and not self.joined:
            if measured is not None:
                condition = (measured > 0 if guard == 'naive'
                             else measured-error >= marker if guard == 'monotone_only'
                             else measured-error-age_loss >= marker)
                self.joined = condition
            if not self.joined:
                if cell == self.reference[self.cursor]:
                    self.cursor += 1
                else:
                    return Command(write=(self.cursor, self.reference[self.cursor]))
                self.ready = self.cursor == len(self.reference)
        return Command(self.force if self.ready or self.joined else F(0))


class Clamp:
    def __init__(self, image=(1, 0, 1), adversary=0, noise=0, age=0, phase=0,
                 cutoff=None, guard='robust', weak=False, unavailable=False,
                 stale_cells=False, descending_history=False, old_positive=False,
                 alias=False, direct=False):
        self.intended = tuple(image)  # Verdict ghost, never passed to the policy.
        self.length = len(image)
        self.error, self.max_age = F(1, 5), 2
        self.response, self.delay = 3, 2
        self.speed, self.theta, self.hostile_cap = F(1), F(3), F(2)
        self.actual_speed, self.damping = F(1), F(1)
        self.speed_lower, self.theta_upper, self.damping_upper = F(1), F(3), F(1)
        self.marker = F(1, 2)
        self.detect = self.marker+2*self.error+2*self.speed*self.max_age
        self.join_delay = 2*self.response+2*self.delay
        self.cutoff = F(16) if cutoff is None else F(cutoff)
        self.limit = F(22)
        self.q, self.tick = F(0), 0
        self.history = [F(0)]  # Physical trajectory ghost, not controller memory.
        self.bodies = list(range(5))
        self.images = [[9]*self.length for _ in range(5)]
        self.producers = [Producer(tuple(image), F(1) if weak else F(2)) for _ in range(4)]
        self.outputs = [Command() for _ in range(4)]
        self.packets = []
        self.periods = [1, 2, 3, 3]
        self.offsets = [(i+phase) % p for i, p in enumerate(self.periods)]
        self.adversary, self.noise, self.age, self.phase = adversary, noise, age, phase
        self.guard, self.unavailable, self.stale_cells = guard, unavailable, stale_cells
        self.descending_history, self.old_positive = descending_history, old_positive
        self.alias, self.direct = alias, direct
        self.first_motion = self.first_detect = self.first_cut = self.finished = None
        self.witnesses = []
        self.all_applied_at_cut = None
        self.cut_force_gap = False
        self.work = F(0)
        self.write_attempts = self.rejected_writes = self.direct_events = 0
        self.nominal_writes_before_detection = 0
        self.samples = self.command_deliveries = 0
        self.injected = False
        self.kicked = False

    def observe(self, who):
        self.work += 1
        self.samples += 1
        if self.unavailable:
            return None
        age = 0 if self.age == 0 else self.max_age if self.age == 1 else (self.tick+who) % (self.max_age+1)
        sampled = self.tick-age
        actual = (F(-sampled)*self.speed if self.descending_history else F(0)) if sampled < 0 else self.history[sampled]
        noise = -self.error if self.noise == 0 else self.error if self.noise == 1 else (-self.error, F(0), self.error)[(self.tick+who) % 3]
        return actual+noise

    def own_read(self, who):
        self.work += 1
        cursor = self.producers[who].cursor
        if cursor >= self.length:
            return None
        return self.intended[cursor] if self.stale_cells else self.images[who][cursor]

    def write(self, who, address, value, bypass=False):
        self.work += 1
        self.write_attempts += 1
        if (bypass or self.q < self.cutoff) and 0 <= address < self.length and 0 <= value < 256:
            self.images[who][address] = value
            if who < len(self.producers) and 0 < self.q < self.detect:
                self.nominal_writes_before_detection += 1
        else:
            self.rejected_writes += 1

    def opposing(self):
        if self.adversary == 0:
            return -self.hostile_cap
        if self.adversary == 1:
            return self.hostile_cap
        if self.adversary == 2:
            return (-self.hostile_cap, self.hostile_cap, F(0))[self.tick % 3]
        if self.adversary == 3:
            nominal = sum((c.force for c in self.outputs), F(0))
            kick = self.theta-nominal+F(1,10)
            if (not self.kicked and self.q == 0 and nominal > 0
                    and abs(kick) <= self.hostile_cap and nominal <= self.theta+self.hostile_cap):
                self.kicked = True
                # Bounded assistance produces actual motion0.1, then ceases.
                return kick
            return -self.hostile_cap
        if self.adversary == 4:
            return self.hostile_cap if self.q < self.cutoff else -self.hostile_cap
        raise RuntimeError('Unknown bounded force profile')

    def step(self):
        due = [p for p in self.packets if p[0] <= self.tick]
        self.packets = [p for p in self.packets if p[0] > self.tick]
        for _, who, command in due:
            self.outputs[who] = command
            self.command_deliveries += 1
            self.work += 1
        for who, producer in enumerate(self.producers):
            if self.tick % self.periods[who] == self.offsets[who]:
                self.work += 1
                command = producer.invoke(self.observe(who), self.error,
                                          self.speed*self.max_age, self.marker,
                                          self.own_read(who), self.guard)
                lag = (2*self.tick+who+self.phase) % (self.delay+1)
                self.work += 1  # Every bounded command admission is charged.
                if lag:
                    self.packets.append((self.tick+lag, who, command))
                else:
                    self.outputs[who] = command
                    self.command_deliveries += 1
                    self.work += 1
        if self.old_positive and not self.injected:
            # Previous-attempt close packets arriving after the alleged drain.
            self.outputs = [Command(p.force) for p in self.producers]
            self.command_deliveries += len(self.producers)
            self.work += len(self.producers)
            self.injected = True
        for who, command in enumerate(self.outputs):
            require(F(0) <= command.force <= self.producers[who].force, 'Closing-fragment force alphabet violated')
            if command.write is not None:
                self.write(who, *command.write)
        # Existing hostile code writes continuously through its own ordinary lead.
        self.write(4, self.tick % self.length, 9)
        if self.alias and self.first_motion is not None:
            # Removed private-port hypothesis: an old sibling can reach this bay.
            for who in self.witnesses:
                if self.q < self.cutoff:
                    self.write(who, 0, 9)
        if self.direct and self.first_cut is not None and not self.injected:
            for who in self.witnesses:
                self.images[who][0] = 9
                self.direct_events += 1
            self.injected = True
        hostile = self.opposing()
        require(abs(hostile) <= self.hostile_cap, 'Hostile force bound violated')
        effort = sum((c.force for c in self.outputs), F(0))+hostile
        velocity = max(-self.actual_speed, min(self.actual_speed, dz(effort, self.theta)/self.damping))
        next_q = max(F(0), min(self.limit, self.q+velocity))
        if self.q == 0 and next_q > 0 and self.first_motion is None:
            self.first_motion = F(self.tick)
            self.witnesses = [i for i, p in enumerate(self.producers)
                              if p.ready and self.outputs[i].force > 0 and tuple(self.images[i]) == self.intended]
        for threshold, field in ((self.detect, 'first_detect'), (self.cutoff, 'first_cut'), (self.limit, 'finished')):
            if getattr(self, field) is None and self.q < threshold <= next_q:
                setattr(self, field, F(self.tick)+(threshold-self.q)/velocity)
                if field == 'first_cut':
                    self.all_applied_at_cut = all(c.force == p.force for c, p in zip(self.outputs, self.producers))
        if self.first_cut is not None and not all(c.force == p.force for c, p in zip(self.outputs, self.producers)):
            self.cut_force_gap = True
        self.work += 1+sum((abs(c.force) for c in self.outputs), F(0))+abs(hostile)
        self.q = next_q
        self.tick += 1
        self.history.append(self.q)

    def deadline(self):
        copy = (3*self.length+2)*self.response+(2*self.length+2)*self.delay
        margin = (sum(p.force for p in self.producers)-self.hostile_cap-self.theta_upper)/self.damping_upper
        travel = math.ceil(self.limit/min(self.speed_lower, margin)) if margin > 0 else math.ceil(self.limit/self.speed)
        return copy+self.join_delay+travel

    def run(self, horizon=None):
        for _ in range(self.deadline() if horizon is None else horizon):
            self.step()
        return self.summary()

    def summary(self):
        step_cap = F(2)+sum(p.force for p in self.producers)+self.hostile_cap+len(self.producers)*(self.delay+7)
        return {'ticks': self.tick, 'deadline': self.deadline(), 'q': str(self.q),
                'detection_level': str(self.detect), 'cutoff': str(self.cutoff),
                'join_delay': self.join_delay, 'first_motion': str(self.first_motion),
                'first_detection': str(self.first_detect), 'first_cutoff': str(self.first_cut),
                'finished': str(self.finished), 'first_completed_witnesses': self.witnesses,
                'witnesses_still_correct': [j for j in self.witnesses if tuple(self.images[j]) == self.intended],
                'all_applied_at_cutoff': self.all_applied_at_cut,
                'force_gap_after_cutoff': self.cut_force_gap,
                'ready': [p.ready for p in self.producers], 'joined': [p.joined for p in self.producers],
                'write_attempts': self.write_attempts, 'rejected_writes': self.rejected_writes,
                'nominal_writes_during_subdetectable_motion': self.nominal_writes_before_detection,
                'direct_events': self.direct_events, 'samples': self.samples,
                'command_deliveries': self.command_deliveries,
                'charged_work': str(self.work), 'work_upper_bound': str(step_cap*self.tick)}


def positive_checks():
    count, latest, max_work = 0, F(0), F(0)
    partial_join_histories = 0
    representative = None
    for image, adversary, noise, age, phase in product(product((0, 1), repeat=3), range(4), range(3), range(3), range(2)):
        model = Clamp(image, adversary, noise, age, phase)
        result = model.run()
        require(model.finished is not None and model.finished <= model.deadline(), 'Delayed cutoff did not close within bound')
        require(model.witnesses and result['witnesses_still_correct'] == model.witnesses, 'Completed-image witness was lost')
        require(model.all_applied_at_cut and not model.cut_force_gap, 'Cutoff preceded persistent nominal effort')
        require(all(a <= b for a, b in zip(model.history, model.history[1:])), 'Monotonicity failed')
        require(model.first_cut > model.first_detect+model.join_delay, 'Raw speed/travel ordering failed')
        require(F(result['charged_work']) <= F(result['work_upper_bound']), 'Charged work exceeded bound')
        require(model.rejected_writes > 0 and model.direct_events == 0, 'Continuing old writes were not represented')
        latest, max_work = max(latest, model.finished), max(max_work, model.work)
        representative = representative or result
        partial_join_histories += any(p.joined and not p.ready for p in model.producers)
        count += 1
    require(partial_join_histories > 0, 'Checks exercised only complete-copy closure, not joining')
    sizes = []
    for length in (1, 8, 64, 257):
        model = Clamp(tuple((17*i+3) % 256 for i in range(length)), adversary=3, noise=0, age=1, phase=1)
        result = model.run()
        require(model.finished is not None and model.all_applied_at_cut and result['witnesses_still_correct'], 'Larger copy failed')
        sizes.append({'cells': length, 'finished': str(model.finished), 'deadline': model.deadline()})
    return {'histories': count, 'partial_producer_join_histories': partial_join_histories,
            'latest_finish': str(latest), 'maximum_work': str(max_work),
            'representative': representative, 'image_sizes': sizes}


def failures():
    cases = {}
    early = Clamp((1,)*8, adversary=3, noise=0, age=1, cutoff=F(1,10))
    early.images[0] = list(early.intended)
    r = early.run()
    require(early.first_cut is not None and early.finished is None and early.q < early.detect,
            'Undetectably early cutoff did not expose the stall')
    require(r['witnesses_still_correct'], 'Stall should preserve, not invent loss of, the good candidate')
    cases['early_cutoff_stall'] = r
    delayed = Clamp((1,)*8, adversary=3, noise=0, age=1)
    delayed.images[0] = list(delayed.intended)
    r = delayed.run()
    require(delayed.finished is not None and delayed.nominal_writes_before_detection > 0
            and r['witnesses_still_correct'], 'Delayed cutoff failed to preserve actual copy work during the hidden-motion stall')
    cases['same_small_motion_delayed_cutoff'] = r
    short = Clamp((1,)*8, adversary=1, noise=0, age=1, cutoff=F(5))
    r = short.run()
    require(short.first_cut is not None and not short.all_applied_at_cut and short.finished is not None,
            'Missing response margin should violate ordering without asserting impossibility')
    cases['insufficient_response_margin_only'] = r
    naive = Clamp((1,)*8, adversary=1, noise=1, age=0, guard='naive')
    r = naive.run()
    require(naive.finished is not None and not naive.witnesses, 'Positive-noise false join missing')
    cases['positive_noise_false_join'] = r
    cheap = Clamp((1,)*8, adversary=1, noise=1, age=1, guard='monotone_only', descending_history=True)
    r = cheap.run()
    require(cheap.finished is not None and not cheap.witnesses, 'Pre-reset sample countercase missing')
    cases['pre_reset_sample_without_rate_allowance'] = r
    robust = Clamp((1,)*8, adversary=1, noise=1, age=1, descending_history=True)
    r = robust.run()
    require(robust.finished is not None and r['witnesses_still_correct'], 'Rate-robust guard did not survive pre-reset samples')
    cases['same_pre_reset_history_robust_guard'] = r
    late = Clamp((1,)*64, adversary=1, noise=0, age=1, old_positive=True)
    r = late.run()
    require(late.finished is not None and not late.witnesses, 'Old closing command countercase missing')
    cases['undrained_old_close'] = r
    unread = Clamp((1,)*64, adversary=4, noise=0, age=1, unavailable=True)
    r = unread.run()
    require(unread.first_cut is not None and unread.finished is None, 'Missing recognition availability did not matter')
    cases['missing_position_availability'] = r
    stale = Clamp((1,)*8, adversary=1, stale_cells=True)
    r = stale.run()
    require(stale.finished is not None and not stale.witnesses, 'Stale code equality certified an actual candidate')
    cases['stale_code_readback'] = r
    weak = Clamp((1,)*8, adversary=0, weak=True)
    r = weak.run()
    require(all(p.ready for p in weak.producers) and weak.first_motion is None, 'Insufficient raw force boundary missing')
    cases['insufficient_force'] = r
    alias = Clamp((1,)*8, adversary=1, alias=True)
    r = alias.run()
    require(alias.witnesses and not r['witnesses_still_correct'] and alias.direct_events == 0, 'Old writer alias was charged as fresh corruption')
    cases['retained_writer_alias'] = r
    direct = Clamp((1,)*8, adversary=1, direct=True)
    r = direct.run()
    require(direct.direct_events > 0 and not r['witnesses_still_correct'], 'Direct frozen-image corruption was excluded silently')
    cases['direct_corruption_after_cutoff'] = r
    return cases


def entry_checks():
    checked = 0
    for response, delay, phase in product((1, 3, 5), (0, 1, 3), range(3)):
        unlock = response+2*delay+2
        output = Command(F(2), (0,9))
        # Two arbitrary old close packets are already in flight at entry.
        queue = [(0, Command(F(2), (0,9))), (delay, Command(F(2), (0,9)))]
        local = {'joined': True, 'cursor': 99, 'reference': (7, 8)}
        for t in range(unlock):
            due = [p for p in queue if p[0] <= t]
            queue = [p for p in queue if p[0] > t]
            for _, value in due:
                output = value
            if t % response == phase % response:
                local['joined'], local['cursor'] = False, 0
                lag = (t+phase) % (delay+1)
                if lag:
                    queue.append((t+lag, Command()))
                else:
                    output = Command()
        require(output.force == 0 and output.write is None and not local['joined'] and local['cursor'] == 0,
                'Bounded old commands survived physical reset hold')
        require(local['reference'] == (7,8), 'Reset secretly repaired reference data')
        checked += 1
    return {'histories': checked, 'scope': 'Conditional nominal reset instructions while a real interlock holds q=0; no arbitrary-cycle restart theorem.'}


def uncertain_mechanics_checks():
    checked, latest = 0, F(0)
    for theta, damping, actual_cap in product((F(3),F(13,4),F(7,2)),
                                             (F(1),F(3,2),F(2)),
                                             (F(1,2),F(3,4),F(1))):
        model = Clamp((1,)*8, adversary=2, noise=0, age=1, phase=1)
        model.theta, model.damping, model.actual_speed = theta, damping, actual_cap
        # One controller and geometry use these common design bounds in all cases.
        model.theta_upper, model.damping_upper, model.speed_lower = F(7,2),F(2),F(1,2)
        result = model.run()
        require(model.detect == F(49,10) and model.cutoff == 16 and model.deadline() == 168,
                'Policy/geometry secretly specialized to actual parameters')
        require(model.finished is not None and model.finished <= model.deadline()
                and model.all_applied_at_cut and result['witnesses_still_correct'],
                'Uniform mechanical envelope failed')
        latest = max(latest,model.finished)
        checked += 1
    return {'histories':checked,'theta_interval':['3','7/2'],'damping_interval':['1','2'],
            'speed_cap_interval':['1/2','1'],'uniform_progress_lower':'1/2',
            'common_deadline':168,'latest_finish':str(latest)}


def check_lean(name, namespace, lean):
    source = (HERE/name).read_text(encoding='utf-8')
    clean = re.sub(r'/\-.*?\-/', '', source, flags=re.S)
    require(not re.search(r'\b(sorry|axiom|unsafe|implemented_by)\b', clean), 'Unapproved proof escape')
    run = subprocess.run([str(lean), str(HERE/name)], cwd=HERE, text=True, encoding='utf-8', capture_output=True)
    require(run.returncode == 0 and not run.stderr.strip(), run.stdout+run.stderr)
    names = re.findall(r'^theorem (\w+)', source, flags=re.M)
    require(set(names) == set(re.findall(r'^#print axioms (\w+)', source, flags=re.M)), 'Incomplete declaration inventory')
    inventory = {}
    for short in names:
        line = next((x for x in run.stdout.splitlines() if x.startswith("'"+namespace+'.'+short+"'")), None)
        require(line is not None and 'sorryAx' not in line, 'Unchecked declaration '+short)
        deps = re.search(r'depends on axioms: \[(.*?)\]', line)
        require(not deps or set(deps.group(1).split(', ')) <= {'propext','Classical.choice','Quot.sound'}, 'Unexpected axiom')
        inventory[short] = line
    return inventory


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    parser.add_argument('--lean', type=Path, default=LEAN)
    args = parser.parse_args()
    names = ('CLAMP.md','Clamp.lean','clamp_model.py','Operations.lean')
    hashes = lambda: {name:sha256((HERE/name).read_bytes().replace(b'\r\n',b'\n')).hexdigest() for name in names}
    before = hashes()
    version = subprocess.run([str(args.lean),'--version'],text=True,encoding='utf-8',capture_output=True)
    require(version.returncode == 0 and 'version 4.33.0,' in version.stdout,'Lean4.33.0 required')
    result = {'schema':'delayed-noisy-clamp-v1','status':'passed','definition_base':'507ed22',
              'scope':'Conditional physical clamp/copy fragment, not full cyclic entry, code-read availability, source admission or recurring useful service.',
              'sources_sha256_lf':before,'lean_version':version.stdout.strip(),
              'new_lean':check_lean('Clamp.lean','ByzantineNoisyClamp',args.lean),
              'reused_force_lean':check_lean('Operations.lean','ByzantineLocalOperations',args.lean),
              'positive':positive_checks(),'entry':entry_checks(),
              'uncertain_mechanics':uncertain_mechanics_checks(),'comparisons':failures()}
    require(before == hashes(), 'Sources changed during checking')
    encoded = json.dumps(result,indent=2,sort_keys=True)+'\n'
    target = HERE/'clamp_results.json'
    if args.write:
        target.write_text(encoded,encoding='utf-8',newline='\n')
    else:
        require(target.read_text(encoding='utf-8') == encoded, 'Record differs; review before refresh')
    print(json.dumps({'status':'passed','new_lean':len(result['new_lean']),
                      'positive_histories':result['positive']['histories'],
                      'entry_histories':result['entry']['histories'],
                      'comparison_cases':len(result['comparisons'])}))


if __name__ == '__main__':
    main()
