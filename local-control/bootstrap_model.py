"""Elementary mutable-code prefix; main is only an observation boundary."""
from dataclasses import dataclass, field
from itertools import product
from pathlib import Path
from hashlib import sha256
import argparse
import json
import sys

if sys.flags.optimize:
    raise RuntimeError('Unoptimized Python is required')

HERE = Path(__file__).resolve().parent


def require(p, message):
    if not p:
        raise RuntimeError(message)


def prefix(q):
    return [('li', 0, 0), ('li', 1, 0), ('li', 2, q),
            ('store', 0, 1), ('add1', 0), ('ltjump', 0, 2, 3), ('jump', 7)]


@dataclass
class Machine:
    code: list
    work: list
    regs: list
    incoming: list = field(default_factory=lambda: [99, 101])
    external: list = field(default_factory=lambda: ['old-held-force', 'old-inflight-packet'])
    new_side_driver: list = field(default_factory=lambda: [2, -2, 1])
    keeper_side_driver: list = field(default_factory=lambda: [2, 2, 2])
    pc: int = 0
    width: int = 16
    steps: int = 0
    issued: list = field(default_factory=list)

    def step(self):
        require(0 <= self.pc < len(self.code), 'Instruction outside prefix')
        ins = self.code[self.pc]
        self.pc += 1
        self.steps += 1
        op = ins[0]
        if op == 'li':
            self.regs[ins[1]] = ins[2]
        elif op == 'store':
            address = self.regs[ins[1]]
            if 0 <= address < len(self.work):
                self.work[address] = self.regs[ins[2]]
        elif op == 'add1':
            self.regs[ins[1]] = (self.regs[ins[1]] + 1) % (1 << self.width)
        elif op == 'ltjump':
            if self.regs[ins[1]] < self.regs[ins[2]]:
                self.pc = ins[3]
        elif op == 'jump':
            self.pc = ins[1]
        elif op == 'emit':
            self.issued.append(ins[1])
        else:
            raise RuntimeError('Unknown probe instruction')

    def run(self, hook=None, limit=None):
        cap = 3 * len(self.work) + 4 if limit is None else limit
        for t in range(cap):
            if self.pc == 7:
                return
            if hook:
                hook(self, t)
            self.step()


def checks():
    count = 0
    for q in (1, 2, 3, 4):
        for initial in product(range(3), repeat=q + 3):
            machine = Machine(prefix(q), list(initial[:q]), list(initial[q:]))
            def hostile_input(m, t):
                m.incoming[:] = [(t * 31) % 65536, 65535 - t]
            machine.run(hostile_input)
            require(machine.pc == 7 and machine.work == [0] * q, 'Prefix failed')
            require(machine.steps == 3 * q + 4, 'Instruction bound failed')
            require(machine.code == prefix(q) and not machine.issued, 'Prefix changed code or emitted')
            require(machine.external == ['old-held-force', 'old-inflight-packet'], 'Prefix erased external effects')
            require(machine.regs == [q, 0, q], 'Exit register postcondition changed')
            require(machine.new_side_driver == [2, -2, 1] and machine.keeper_side_driver == [2, 2, 2],
                    'Private stores silently cleared a physical driver')
            count += 1
    large = []
    for q in (32, 1024, 8192):
        machine = Machine(prefix(q), [65535] * q, [65535] * 3)
        machine.run()
        require(machine.work == [0] * q and machine.steps == 3 * q + 4, 'Larger prefix failed')
        large.append({'words': q, 'instructions': machine.steps})
    missing = Machine(prefix(3), [9] * 3, [9] * 3, pc=7)
    missing.run()
    require(missing.work != [0] * 3, 'Missing reset counterexample failed')
    corrupt = Machine(prefix(3), [9] * 3, [9] * 3)
    corrupt.code[0] = ('jump', 7)
    corrupt.run()
    require(corrupt.pc == 7 and corrupt.work != [0] * 3, 'Corrupt entry counterexample failed')
    race = Machine(prefix(3), [9] * 3, [9] * 3)
    race.run(lambda m, t: m.work.__setitem__(0, 8) if t == 12 else None)
    require(race.pc == 7 and race.work[0] == 8, 'Late writer counterexample failed')
    interrupted = Machine(prefix(3), [9] * 3, [9] * 3)
    interrupted.run(limit=4)
    require(interrupted.work == [0, 9, 9] and interrupted.pc != 7, 'Interrupted prefix was rolled back')
    delayed = Machine(prefix(3), [9] * 3, [9] * 3)
    delayed.run()
    delayed.incoming[:] = [600, 600]
    require(delayed.work == [0] * 3 and delayed.incoming == [600, 600], 'Input separation failed')
    return {
        'status': 'passed conditional stored-prefix checks; controller and source suppliers open',
        'exhaustive_small_initializations': count,
        'larger_sizes': large,
        'countercases': {
            'missing_reset_entry': missing.work,
            'corrupted_stored_entry': corrupt.work,
            'late_private_writer': race.work,
            'interrupted_prefix': interrupted.work,
            'stale_input_after_main': delayed.incoming,
            'retained_external_effects': delayed.external,
            'uncleared_new_side_driver': delayed.new_side_driver,
            'preserved_keeper_side_driver': delayed.keeper_side_driver,
        },
        'inputs': {name: sha256((HERE / name).read_text(encoding='utf-8').replace('\r\n', '\n').encode()).hexdigest()
                   for name in ('BOOTSTRAP.md', 'bootstrap_model.py')},
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--check', action='store_true')
    group.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = checks()
    path = HERE / 'bootstrap_results.json'
    if args.write:
        path.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    else:
        require(result == json.loads(path.read_text(encoding='utf-8')), 'Frozen record differs')
    print(result['status'])
