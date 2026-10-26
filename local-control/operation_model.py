"""One-host final-dock reconstruction kernel and source-bound conditional checks.

This is an event/stroke realization of OPERATIONS.md, not a global repair server.
The target CPU diagnostic is deliberately not counted as mission service.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass, field
from hashlib import sha256
from itertools import product
import json
import os
from pathlib import Path
import re
import subprocess
import sys

if sys.flags.optimize:
    raise RuntimeError('Unoptimized Python is required')

HERE = Path(__file__).resolve().parent
DEFAULT_LEAN = Path(os.environ['USERPROFILE']) / '.elan/toolchains/leanprover--lean4---v4.33.0/bin/lean.exe'


def require(value, message):
    if not value:
        raise RuntimeError(message)


def deadzone(force, threshold):
    return force - threshold if force > threshold else force + threshold if force < -threshold else 0


def stroke(position, force, limit, threshold=3, speed=1):
    displacement = max(-speed, min(speed, deadzone(force, threshold)))
    return max(0, min(limit, position + displacement))


@dataclass(frozen=True)
class Command:
    reset: int = 0
    insert: int = 0
    freeze: int = 0
    activate: int | None = None
    activation_force: int = 0
    write: tuple[int, int] | None = None
    cut: int = 0


@dataclass
class Body:
    identity: int
    host: int
    memory: list[int]
    latent_cpu_fault: bool = False


@dataclass
class Actor:
    """Mutable local state. No faulty-set, intended-image or analyst time input."""
    index: int
    reference: list[int]
    force: int = 2
    cursor: int = 91
    ready: bool = False
    scan_bay: int = 88
    scan_address: int = 71
    scan_match: bool = False
    accepted: list[bool] = field(default_factory=list)
    read_ids: list[int | None] = field(default_factory=list)
    selected: int | None = None
    rejected: bool = False

    def invoke(self, view, read_cell):
        count = view['bays']
        if view['reset'] < view['reset_limit']:
            # These assignments execute in the current mutable program. The source
            # reset coordinate does not itself rewrite any actor or its reference.
            self.cursor = self.scan_bay = self.scan_address = 0
            self.ready = self.rejected = False
            self.scan_match = True
            self.accepted = [False] * count
            self.read_ids = [None] * count
            self.selected = None
            return Command(reset=self.force, insert=self.force)
        if view['cut'] < view['cut_limit']:
            # The hardware is norm-blind. This is a software decision from a
            # supplied factual envelope that must remain valid through the stroke.
            return Command(cut=self.force if view['load_upper'] <= view['safe_load'] else 0)
        if view['freeze'] == 0:
            if view['insertions'][self.index] != view['insertion_limits'][self.index]:
                return Command(insert=self.force)
            if self.cursor < len(self.reference):
                value = read_cell(self.index, self.cursor)
                if value == self.reference[self.cursor]:
                    self.cursor += 1
                else:
                    return Command(insert=self.force, write=(self.cursor, self.reference[self.cursor]))
            self.ready = self.cursor == len(self.reference)
            return Command(insert=self.force, freeze=self.force if self.ready else 0)
        if view['freeze'] < view['freeze_limit']:
            # A partial writer does not wait for a disconnected write acknowledgment.
            return Command(freeze=self.force)
        if self.scan_bay < count:
            bay = self.scan_bay
            identity = view['body_ids'][bay]
            if self.scan_address == 0:
                self.scan_match = True
                self.read_ids[bay] = identity
            value = read_cell(bay, self.scan_address)
            self.scan_match = self.scan_match and identity == self.read_ids[bay] and value == self.reference[self.scan_address]
            self.scan_address += 1
            if self.scan_address == len(self.reference):
                self.accepted[bay] = self.scan_match
                self.scan_bay += 1
                self.scan_address = 0
            if self.scan_bay < count:
                return Command()
            self.selected = next((j for j, ok in enumerate(self.accepted) if ok), None)
            self.rejected = self.selected is None
        if self.selected is None:
            return Command()
        return Command(activate=self.selected, activation_force=self.force)


class Host:
    def __init__(self, image=(1, 0, 1), bad=0, pattern=(0, 0, 0), schedule=0,
                 weak=False, all_off=False, latent=False):
        self.image = tuple(image)  # Analyst's verdict only; neither dynamics nor actors read this.
        self.bays = 5
        self.length = len(image)
        self.delay = 3
        self.response = 5
        self.reset_limit = 2 * self.delay + self.response + 2
        self.freeze_limit = 5
        self.cut_limit = 6
        self.insertion_limits = [2, 4, 3, 5, 2]
        self.scan_bound = (self.bays * self.length + 2) * self.response
        self.power_at = self.scan_bound + 2
        self.activation_limit = self.power_at + 3
        self.reset = self.freeze = 0
        self.cut = 0
        self.load = 3
        self.load_upper = 4
        self.safe_load = 5
        self.insertions = [0] * self.bays
        self.activation = [0] * self.bays
        self.body_at_bay = list(range(self.bays))
        self.bodies = {j: Body(j, 0, [9] * self.length, latent and j == 0) for j in range(self.bays)}
        self.actors = [Actor(j, list(image)) for j in range(self.bays)]
        self.bad = {bad} if not weak else {0, 1, 2}
        self.nominal = [j for j in range(self.bays) if j not in self.bad]
        self.pattern = pattern
        self.all_off = all_off
        self.periods = ([2, 3, 4, 5, 2] if schedule == 0 else [5, 2, 3, 2, 4])
        self.offsets = [(j + schedule) % self.periods[j] for j in range(self.bays)]
        self.outputs = [Command(freeze=2, activate=0, activation_force=2, write=(0, 8)) for _ in range(self.bays)]
        # Initial packets are genuinely old commands, all delivered within D.
        self.packets = [(j % (self.delay + 1), j, Command(freeze=2, write=(0, 8))) for j in range(self.bays)]
        self.old_writer_attempts = self.old_writer_rejections = 0
        self.old_pending = [(d, 100 + d) for d in range(1, 6)]
        self.old_deliveries = []
        self.retained_knowledge = {'old_credential', 'old_image'}
        self.tick = 0
        self.work = self.reads = self.invocations = self.writes = self.rejected_writes = 0
        self.starts = []
        self.diagnostic_outputs = []
        self.first_freeze = None
        self.freeze_witness = None
        self.frozen_at = None
        self.selected_at = {}
        self.injections = []
        self.direct_events = 0

    def view(self):
        return {'bays': self.bays, 'reset': self.reset, 'reset_limit': self.reset_limit,
                'freeze': self.freeze, 'freeze_limit': self.freeze_limit,
                'cut': self.cut, 'cut_limit': self.cut_limit,
                'load_upper': self.load_upper, 'safe_load': self.safe_load,
                'insertions': tuple(self.insertions), 'insertion_limits': tuple(self.insertion_limits),
                'body_ids': tuple(self.body_at_bay)}

    def powered(self, bay):
        return (bay == 0 and self.cut < 2) or self.activation[bay] >= self.power_at

    def read(self, actor, bay, address):
        self.reads += 1
        self.work += 1
        if not (0 <= bay < self.bays and 0 <= address < self.length):
            return None
        if self.insertions[bay] != self.insertion_limits[bay] or self.powered(bay):
            return None
        # Passive cell read: no target-program response or intended-image test.
        return self.bodies[self.body_at_bay[bay]].memory[address]

    def adversarial_output(self, actor):
        bit = self.pattern[self.tick % len(self.pattern)]
        sign = -1 if bit == 0 else 1
        target = next(iter(self.selected_at.values()))[0] if self.selected_at else 0
        return Command(reset=sign * 2, insert=-2, freeze=sign * 2,
                       activate=target, activation_force=sign * 2,
                       write=(self.tick % self.length, 9), cut=sign * 2)

    def ordinary_write(self, producer, address, value):
        self.work += 1  # Failed requests still cost work; they are not fresh intrusions.
        if (0 <= producer < self.bays and 0 <= address < self.length and 0 <= value < 256
                and self.reset == self.reset_limit and self.cut == self.cut_limit and self.freeze == 0
                and self.insertions[producer] == self.insertion_limits[producer]
                and not self.powered(producer)):
            self.bodies[self.body_at_bay[producer]].memory[address] = value
            self.writes += 1
        else:
            self.rejected_writes += 1

    def corrupt(self, bay, value, cause):
        self.bodies[self.body_at_bay[bay]].memory[0] = value
        self.injections.append({'tick': self.tick, 'cause': cause, 'bay': bay})
        if cause == 'fresh_direct_digital_corruption':
            self.direct_events += 1

    def step(self, hook=None):
        if hook:
            hook(self)
        due = [p for p in self.packets if p[0] <= self.tick]
        self.packets = [p for p in self.packets if p[0] > self.tick]
        for _, actor, command in due:
            self.outputs[actor] = command
        for actor in self.bad:
            self.outputs[actor] = self.adversarial_output(actor)
        if self.all_off:
            for actor in self.nominal:
                self.outputs[actor] = Command()
        else:
            for j in self.nominal:
                if self.tick % self.periods[j] == self.offsets[j]:
                    self.invocations += 1
                    self.work += 1
                    command = self.actors[j].invoke(self.view(), lambda b, a, j=j: self.read(j, b, a))
                    lag = (self.tick + j) % (self.delay + 1)
                    if lag == 0:
                        self.outputs[j] = command
                    else:
                        self.packets.append((self.tick + lag, j, command))
                    if self.actors[j].selected is not None and j not in self.selected_at:
                        self.selected_at[j] = (self.actors[j].selected, self.tick)
        for j, command in enumerate(self.outputs):
            require(max(abs(command.reset), abs(command.insert), abs(command.freeze), abs(command.activation_force), abs(command.cut)) <= 2,
                    'Per-port force violated')
            self.work += abs(command.reset) + self.bays * abs(command.insert) + abs(command.freeze) + abs(command.activation_force) + abs(command.cut)
            if command.write is not None:
                self.ordinary_write(j, *command.write)
        # Previously acquired authority continues issuing requests, without a new
        # event charge. The cut contacts, not a revoked credential flag, stop it.
        self.old_writer_attempts += 1
        self.work += 1
        if self.cut < 4:
            self.bodies[self.body_at_bay[0]].memory[self.tick % self.length] = 9
        else:
            self.old_writer_rejections += 1
        if self.cut < self.cut_limit:
            self.old_pending.append((self.tick + 5, 200 + self.tick))
            self.work += 1
        previous_power = [self.activation[j] >= self.power_at for j in range(self.bays)]
        previous_q = self.freeze
        # Ordered elementary events: writes; insertions; reset stroke; clamp; activation.
        if self.freeze == 0 and self.cut == self.cut_limit and not any(previous_power):
            effort = sum(c.insert for c in self.outputs)
            self.insertions = [stroke(x, effort, limit) for x, limit in zip(self.insertions, self.insertion_limits)]
        if self.freeze == 0 and not any(self.activation):
            self.reset = stroke(self.reset, sum(c.reset for c in self.outputs), self.reset_limit)
        if self.reset == self.reset_limit and self.freeze == 0 and not any(previous_power):
            self.cut = stroke(self.cut, sum(c.cut for c in self.outputs), self.cut_limit)
        if self.reset == self.reset_limit and self.cut == self.cut_limit and not any(previous_power):
            self.freeze = stroke(self.freeze, sum(c.freeze for c in self.outputs), self.freeze_limit)
        if previous_q == 0 and self.freeze > 0 and self.first_freeze is None:
            self.first_freeze = self.tick
            self.freeze_witness = [j for j in self.nominal
                                   if self.outputs[j].freeze > 0 and self.actors[j].ready
                                   and tuple(self.bodies[self.body_at_bay[j]].memory) == self.image]
        if self.freeze == self.freeze_limit and self.frozen_at is None:
            self.frozen_at = self.tick
        if self.freeze == self.freeze_limit:
            for j in range(self.bays):
                effort = sum(c.activation_force for c in self.outputs if c.activate == j)
                self.activation[j] = stroke(self.activation[j], effort, self.activation_limit)
        for j in range(self.bays):
            if self.activation[j] >= self.power_at and not previous_power[j]:
                body = self.bodies[self.body_at_bay[j]]
                self.starts.append({'tick': self.tick, 'bay': j, 'body': body.identity,
                                    'image': list(body.memory), 'all_nominal_scans_done': len(self.selected_at) == len(self.nominal)})
            if self.activation[j] == self.activation_limit:
                body = self.bodies[self.body_at_bay[j]]
                # A diagnostic transducer reads actual memory; it never tests against intended P.
                value = 77 if body.latent_cpu_fault else body.memory[0]
                self.diagnostic_outputs.append({'tick': self.tick, 'body': body.identity, 'value': value})
        delivering = [p for p in self.old_pending if p[0] <= self.tick]
        self.old_pending = [p for p in self.old_pending if p[0] > self.tick]
        self.old_deliveries.extend(delivering)
        self.work += 1 + len(delivering)
        self.tick += 1

    def bound(self):
        j, d, length, bays = self.response, self.delay, self.length, self.bays
        return (j + 2*d + self.reset_limit + j + 2*d + max(self.insertion_limits)
                + j + 2*d + self.cut_limit
                + (3*length + 2)*j + (2*length + 2)*d + j + 2*d + self.freeze_limit
                + (bays*length + 2)*j + j + 2*d + self.activation_limit + 5 + 3)

    def run(self, hook=None, limit=None):
        for _ in range(self.bound() if limit is None else limit):
            self.step(hook)
            if self.diagnostic_outputs:
                break
        return self.summary()

    def summary(self):
        return {'ticks': self.tick, 'bound': self.bound(), 'starts': self.starts,
                'first_freeze': self.first_freeze, 'freeze_witness': self.freeze_witness,
                'selected': {str(j): value[0] for j, value in self.selected_at.items()},
                'diagnostic': self.diagnostic_outputs[-1] if self.diagnostic_outputs else None,
                'work_charged': self.work,
                'work_upper_bound': self.bound() * (self.bays * (2 * (self.bays + 4) + 3) + 9),
                'reads': self.reads, 'writes': self.writes,
                'rejected_old_writer_requests': self.rejected_writes,
                'direct_events': self.direct_events, 'injections': self.injections,
                'body_at_bay': self.body_at_bay, 'old_pending': self.old_pending,
                'cut_position': self.cut, 'old_writer_attempts': self.old_writer_attempts,
                'old_writer_rejections': self.old_writer_rejections,
                'old_deliveries': {'count': len(self.old_deliveries), 'last': self.old_deliveries[-3:]},
                'retained_knowledge': sorted(self.retained_knowledge)}


def positive_cases():
    count = maximum_time = maximum_work = 0
    representative = None
    for image, bad, pattern, schedule in product(product((0, 1), repeat=3), range(5), product((0, 1), repeat=3), range(2)):
        host = Host(image, bad, pattern, schedule)
        result = host.run()
        require(result['diagnostic'] is not None, 'Conditional attempt failed to finish')
        require(result['ticks'] <= result['bound'], 'Time bound exceeded')
        require(result['work_charged'] <= result['work_upper_bound'], 'Work bound exceeded')
        require(len(result['starts']) == 1 and result['starts'][0]['image'] == list(image), 'Wrong or multiple image starts')
        require(result['starts'][0]['all_nominal_scans_done'], 'Power preceded a nominal scan')
        require(result['freeze_witness'], 'First closing lacked an actually prepared nominal candidate')
        require(len(set(result['selected'].values())) == 1, 'Nominal selections differ')
        require(not result['old_pending'] and result['old_deliveries']['count'] > 5, 'Old effects silently erased')
        require(host.cut == host.cut_limit and host.old_writer_rejections > 0, 'Actual old-port exclusion missing')
        require(result['rejected_old_writer_requests'] > 0 and result['direct_events'] == 0,
                'Ongoing old writer was not represented')
        require(all(body.host == 0 for body in host.bodies.values()), 'Host affinity violated')
        maximum_time = max(maximum_time, result['ticks'])
        maximum_work = max(maximum_work, result['work_charged'])
        representative = representative or result
        count += 1
    return {'cases': count, 'maximum_ticks': maximum_time, 'maximum_work_charged': maximum_work,
            'representative': representative}


def countercases():
    results = {}
    for cause in ('uncut_old_write_path', 'fresh_direct_digital_corruption', 'physical_substitution_after_scan'):
        host = Host(pattern=(0, 0, 0))
        def hook(h, cause=cause):
            if h.injections or len(h.selected_at) != len(h.nominal):
                return
            selected = next(iter(h.selected_at.values()))[0]
            if h.activation[selected] != h.power_at - 1:
                return
            if cause == 'physical_substitution_after_scan':
                other = 0
                h.body_at_bay[selected], h.body_at_bay[other] = h.body_at_bay[other], h.body_at_bay[selected]
                h.injections.append({'tick': h.tick, 'cause': cause, 'bay': selected})
            else:
                h.corrupt(selected, 9, cause)
        result = host.run(hook)
        require(result['starts'] and result['starts'][0]['image'] != list(host.image), cause + ' did not expose failure')
        require(result['direct_events'] == (1 if cause == 'fresh_direct_digital_corruption' else 0), 'Event accounting conflated')
        results[cause] = result
    host = Host(pattern=(0, 0, 0))
    def late(h):
        if h.cut == h.cut_limit and h.freeze == 0 and not h.injections:
            # A legitimately emitted old closing command arrives beyond the admitted drain bound.
            for j in h.nominal:
                h.outputs[j] = Command(freeze=2)
            h.injections.append({'tick': h.tick, 'cause': 'late_old_nominal_closing_commands'})
    result = host.run(late)
    require(not result['starts'] and not result['freeze_witness'], 'Late-command false first-closing argument not exposed')
    require(all(a.rejected for j, a in enumerate(host.actors) if j in host.nominal), 'Frozen partial images were not rejected')
    results['late_old_command'] = result
    for name, host in [('insufficient_force', Host(weak=True, pattern=(0, 0, 0))),
                       ('all_guard_executors_off', Host(all_off=True, pattern=(0, 0, 0)))]:
        result = host.run()
        require(not result['starts'] and result['first_freeze'] is None, name + ' unexpectedly progressed')
        results[name] = result
    host = Host(latent=True, pattern=(0, 0, 0))
    # Override only the Byzantine producer's chosen writes, retaining its opposed forces.
    original = host.adversarial_output
    def benign_candidate(j):
        c = original(j)
        return Command(c.reset, c.insert, c.freeze, c.activate, c.activation_force,
                       (host.tick % host.length, host.image[host.tick % host.length]), c.cut)
    host.adversarial_output = benign_candidate
    result = host.run()
    require(result['starts'][0]['bay'] == 0 and result['starts'][0]['image'] == list(host.image), 'Latent body was not selected after correct image')
    require(result['diagnostic']['value'] != host.image[0], 'Image/CPU distinction not exposed')
    results['latent_bad_cpu'] = result
    host = Host(pattern=(0, 0, 0))
    for j in host.nominal:
        host.actors[j].reference[:] = [4] * host.length
    result = host.run()
    require(result['starts'][0]['image'] == [4] * host.length, 'Source secretly enforced the analyst image')
    results['poisoned_maintained_references'] = result
    host = Host(pattern=(0, 0, 0))
    genuine_read = host.read
    def forged_read(actor, bay, address):
        value = genuine_read(actor, bay, address)
        return host.actors[actor].reference[address] if host.freeze == host.freeze_limit else value
    host.read = forged_read
    result = host.run()
    require(result['starts'][0]['bay'] == 0 and result['starts'][0]['image'] != list(host.image), 'Shared forged inspection did not expose missing evidence supplier')
    results['shared_forged_inspection_frame'] = result
    host = Host(pattern=(0, 0, 0))
    host.load = host.load_upper = 8
    result = host.run()
    require(host.cut == 0 and not result['starts'], 'High-load operation was not deferred')
    results['permission_unavailable'] = result
    return results


def size_variations():
    cases = []
    for length in (1, 7, 64, 257):
        image = tuple((17 * k + 3) % 256 for k in range(length))
        host = Host(image=image, pattern=(1, 0, 1), schedule=1)
        result = host.run()
        require(result['diagnostic'] is not None and result['ticks'] <= result['bound'], 'Image-size bound failed')
        require(result['starts'][0]['image'] == list(image) and result['starts'][0]['all_nominal_scans_done'],
                'Larger image was not coherently scanned and started')
        require(result['work_charged'] <= result['work_upper_bound'], 'Larger-image work bound failed')
        cases.append({'cells': length, 'ticks': result['ticks'], 'bound': result['bound'],
                      'work_charged': result['work_charged'], 'work_upper_bound': result['work_upper_bound']})
    return cases


def arithmetic_checks():
    held = progress = 0
    for threshold in range(5):
        for force in range(-threshold, threshold + 1):
            for position in range(9):
                require(stroke(position, force, 8, threshold) == position, 'Retention failure')
                held += 1
        for margin, position in product(range(1, 5), range(9)):
            force = threshold + margin
            require(stroke(position, force, 8, threshold) >= min(8, position + 1), 'Progress failure')
            progress += 1
    host = Host()
    host.reset = host.reset_limit
    host.cut = host.cut_limit
    host.insertions = list(host.insertion_limits)
    before = [list(b.memory) for b in host.bodies.values()]
    for producer, address, value in ((0, -1, 1), (0, host.length, 1), (0, 0, 256), (-1, 0, 1)):
        host.ordinary_write(producer, address, value)
    require(before == [b.memory for b in host.bodies.values()] and host.rejected_writes == 4,
            'Malformed write escaped port/address alphabet')
    require(host.read(0, -1, 0) is None and host.read(0, 0, host.length) is None,
            'Malformed read was not a nonblocking error')
    return {'retention_cases': held, 'progress_cases': progress, 'malformed_access_cases': 6}


def lean_check(path):
    version = subprocess.run([str(path), '--version'], text=True, encoding='utf-8', capture_output=True)
    require(version.returncode == 0 and 'version 4.33.0,' in version.stdout, 'Pinned Lean4.33.0 is required')
    result = subprocess.run([str(path), str(HERE/'Operations.lean')], cwd=HERE,
                            text=True, encoding='utf-8', capture_output=True)
    require(result.returncode == 0 and not result.stderr.strip(), result.stdout + result.stderr)
    source = (HERE/'Operations.lean').read_text(encoding='utf-8')
    require(not re.search(r'\b(sorry|axiom|unsafe|implemented_by)\b', re.sub(r'/\-.*?\-/', '', source, flags=re.S)), 'Unapproved proof escape')
    names = re.findall(r'^theorem (\w+)', source, flags=re.M)
    require(set(names) == set(re.findall(r'^#print axioms (\w+)', source, flags=re.M)), 'Incomplete theorem inventory')
    inventory = {}
    for name in names:
        full = 'ByzantineLocalOperations.' + name
        line = next((line for line in result.stdout.splitlines() if line.startswith("'"+full+"'")), None)
        require(line is not None and 'sorryAx' not in line, 'Missing or sorry-dependent declaration: '+name)
        dependencies = re.search(r'depends on axioms: \[(.*?)\]', line)
        if dependencies:
            require(set(dependencies.group(1).split(', ')) <= {'propext', 'Classical.choice', 'Quot.sound'},
                    'Unapproved axiom dependency: ' + line)
        inventory[name] = line
    return version.stdout.strip(), inventory


def main():
    p = argparse.ArgumentParser(description=__doc__)
    mode = p.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    p.add_argument('--lean', type=Path, default=DEFAULT_LEAN)
    args = p.parse_args()
    names = ('OPERATIONS.md', 'Operations.lean', 'operation_model.py')
    hashes = lambda: {n: sha256((HERE/n).read_bytes().replace(b'\r\n', b'\n')).hexdigest() for n in names}
    before = hashes()
    version, inventory = lean_check(args.lean)
    result = {'schema': 'conditional-local-operations-v1', 'status': 'passed',
              'scope': 'Conditional one-host image-start kernel; not global renewal service, mission return, source admission or acceptance.',
              'sources_sha256_lf': before, 'lean_version': version, 'lean_declarations': inventory,
              'arithmetic': arithmetic_checks(), 'positive_executions': positive_cases(),
              'image_size_variations': size_variations(), 'countercases': countercases()}
    require(before == hashes(), 'Sources changed during verification')
    encoded = json.dumps(result, sort_keys=True, indent=2) + '\n'
    output = HERE/'operation_results.json'
    if args.write:
        output.write_text(encoded, encoding='utf-8', newline='\n')
    else:
        require(output.read_text(encoding='utf-8') == encoded, 'Record differs; inspect before deliberate refresh')
    print(json.dumps({'status': 'passed', 'lean_lemmas': len(inventory),
                      'positive_cases': result['positive_executions']['cases'],
                      'countercases': list(result['countercases']),
                      'maximum_ticks': result['positive_executions']['maximum_ticks']}))


if __name__ == '__main__':
    main()
