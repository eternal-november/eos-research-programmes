"""Actual occurrence runtime versus independent restricted transition rules.

Uses stdlib, exact Fraction probabilities, and no output files. Run without -O.
The final repository location discovers the runtime relative to this checker;
--runtime PATH permits execution from a disposable workspace.

The shared parameters are a small defunctionalized syntax, its pure functions,
and its procedure definitions. The independent interpreter implements its own
allocation, readiness, spawn, bind, claim, queue and primitive transition rules.
It never calls Machine.step or any runtime state-transition helper. The runtime
AST compiler and snapshots are explicit interpretation/observation interfaces.
This is a finite diagnostic, not a proof for all runtime constructors or Python.
"""

from collections import defaultdict
from copy import deepcopy
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import argparse
import importlib.util
import json
import sys


@dataclass(frozen=True)
class Expr:
    kind: str
    datum: object = None

    def __call__(self, value):
        if self.kind == "id":
            return value
        assert self.kind == "const"
        return self.datum


ID = Expr("id")


@dataclass(frozen=True)
class Kont:
    kind: str
    data: tuple = ()


@dataclass(frozen=True)
class Code:
    kind: str
    args: tuple = ()


def call(name, value=ID):
    return Code("call", (name, value))


def bind(left, kind, *data):
    return Code("bind", (left, Kont(kind, tuple(data))))


def send(channel, payload):
    return Code("send", (channel, Expr("const", payload)))


def receive(channel):
    return Code("receive", (channel,))


def op(name, argument):
    return Code("op", (name, Expr("const", argument)))


def continuation(kont, value):
    """Declared pure continuation family; no world, raw witness or machine."""
    kind, data = kont.kind, kont.data
    if kind == "bootstrap":
        return call("client", Expr("const", 0))
    if kind == "client_read":
        n, r = value
        assert n == data[0] and r in (0, 1)
        return bind(send("req", (n, r)), "client_sent", n, r)
    if kind == "client_sent":
        n, r = data
        assert isinstance(value, int)  # Send returns a message identity.
        return bind(receive("ack"), "client_ack", n, r)
    if kind == "client_ack":
        n, r = data
        assert value[0] == n and value[1] in (0, 1)
        return bind(op("commit", (n, r, value)), "client_commit", n)
    if kind == "client_commit":
        assert value == data[0] + 1
        return call("client")
    if kind == "server_received":
        assert len(value) == 2
        return bind(op("flip", value), "server_flipped")
    if kind == "server_flipped":
        return bind(send("ack", value), "server_sent")
    if kind == "server_sent":
        return call("server", Expr("const", None))
    if kind == "fifo_bootstrap":
        return bind(send("fifo", "first"), "fifo_sent_first")
    if kind == "fifo_sent_first":
        return bind(send("fifo", "second"), "fifo_sent_second")
    if kind == "fifo_sent_second":
        return Code("ret", (Expr("const", "sender-done"),))
    if kind == "fifo_first":
        return bind(receive("fifo"), "fifo_second", value)
    if kind == "fifo_second":
        return Code("ret", (Expr("const", (data[0], value)),))
    raise AssertionError((kind, data, value))


def procedure(name, value):
    if name == "client":
        assert isinstance(value, int) and value >= 0
        return bind(op("read", value), "client_read", value)
    if name == "server":
        return bind(receive("req"), "server_received")
    if name == "spin":
        return call("spin")
    assert name == "fifo_receiver"
    return bind(receive("fifo"), "fifo_first")


def initial_code(fifo=False):
    child = call("fifo_receiver" if fifo else "server", Expr("const", None))
    return bind(Code("spawn", (child, ID)), "fifo_bootstrap" if fifo else "bootstrap")


def empty_transfer(value, held):
    assert held == ()
    return ()


class CompiledKont:
    def __init__(self, runtime, descriptor):
        self.runtime = runtime
        self.descriptor = descriptor

    def __call__(self, value):
        return compile_code(self.runtime, continuation(self.descriptor, value))


def compile_code(runtime, code):
    kind, args = code.kind, code.args
    if kind == "bind":
        return runtime.Bind(compile_code(runtime, args[0]), CompiledKont(runtime, args[1]))
    if kind == "call":
        return runtime.Call(*args)
    if kind == "spawn":
        return runtime.Spawn(compile_code(runtime, args[0]), empty_transfer, args[1])
    if kind == "send":
        return runtime.Send(args[0], empty_transfer, args[1])
    if kind == "receive":
        return runtime.Receive(*args)
    if kind == "op":
        return runtime.Op(*args)
    assert kind == "ret"
    return runtime.Ret(*args)


def decode_code(runtime, term):
    if isinstance(term, runtime.Bind):
        assert isinstance(term.k, CompiledKont)
        return Code("bind", (decode_code(runtime, term.left), term.k.descriptor))
    if isinstance(term, runtime.Call):
        assert isinstance(term.arg, Expr)
        return Code("call", (term.name, term.arg))
    if isinstance(term, runtime.Spawn):
        assert term.take is empty_transfer and isinstance(term.arg, Expr)
        return Code("spawn", (decode_code(runtime, term.term), term.arg))
    if isinstance(term, runtime.Send):
        assert term.take is empty_transfer and isinstance(term.payload, Expr)
        return Code("send", (term.channel, term.payload))
    if isinstance(term, runtime.Receive):
        return Code("receive", (term.channel,))
    if isinstance(term, runtime.Op):
        assert isinstance(term.arg, Expr)
        return Code("op", (term.name, term.arg))
    assert isinstance(term, runtime.Ret) and isinstance(term.f, Expr)
    return Code("ret", (term.f,))


def runtime_tables(runtime, source, weights):
    tables = {}
    for name in ("read", "flip", "commit"):
        def table(argument, caps, world, stores, name=name):
            assert caps == () and stores == {}
            if name == "read":
                assert argument == world["commits"]
                value = (argument, world["x"])
                updated = dict(world)
            elif name == "flip":
                n, cached = argument
                assert n == world["commits"] and cached in (0, 1)
                updated = {**world, "x": 1 - world["x"]}
                value = (n, updated["x"])
            else:
                n, cached, ack = argument
                assert n == world["commits"] and ack[0] == n and ack[1] in (0, 1)
                updated = {**world, "x": 1 - cached, "commits": n + 1}
                value = n + 1
            result = []
            for index, weight in enumerate(weights if source else (F(1),)):
                next_world = {**updated, "aux": index} if source else dict(updated)
                witness = f"{name}:aux{index}" if source else f"{name}:unit"
                result.append(runtime.Outcome(witness, weight, (1,), name,
                                              runtime.Leaf(value), next_world))
            return (tuple(result),)
        tables[name] = table
    return tables


def runtime_machine(runtime, source, weights, fifo=False, code=None):
    procedures = {name: (lambda value, name=name: compile_code(runtime, procedure(name, value)))
                  for name in ("client", "server", "fifo_receiver", "spin")}
    world = {"x": 0, "commits": 0}
    if source:
        world["aux"] = 0
    return runtime.Machine(compile_code(runtime, initial_code(fifo) if code is None else code), world=world,
                           primitives=runtime_tables(runtime, source, weights), procedures=procedures)


@dataclass
class RuleResult:
    value: object
    raw: tuple
    events: tuple = ()
    status: str = "returned"


@dataclass
class RuleJob:
    code: Code
    value: object
    rank: tuple
    mode: str = "eval"
    waiting: object = None
    result: RuleResult | None = None
    parent: int | None = None
    claimed: bool = False


class RestrictedRules:
    """Independent small-step semantics of the stated unary, empty-token IR."""
    def __init__(self, source, weights, fifo=False, code=None):
        self.source = source
        self.weights = weights
        self.jobs = {0: RuleJob(initial_code(fifo) if code is None else code, None, (0,))}
        self.world = {"x": 0, "commits": 0}
        if source:
            self.world["aux"] = 0
        self.messages = {}
        self.queues = {}
        self.events = []
        self.trace = []
        self.next_job = 1
        self.next_message = 0

    def enabled(self):
        ready = []
        for pid, job in self.jobs.items():
            if job.mode == "done":
                continue
            if job.mode == "left":
                ok = self.jobs[job.waiting[0]].mode == "done"
            elif job.mode == "join":
                ok = all(self.jobs[child].mode == "done" for child in job.waiting["children"])
            elif job.code.kind == "receive":
                ok = bool(self.queues.get(job.code.args[0]))
            else:
                ok = True
            if ok:
                ready.append(pid)
        return ready

    def allocate(self, code, value, rank, parent):
        pid = self.next_job
        self.next_job += 1
        self.jobs[pid] = RuleJob(code, value, rank, parent=parent)
        return pid

    def finish(self, pid, result):
        self.jobs[pid].mode = "done"
        self.jobs[pid].result = result

    def claim(self, pid):
        child = self.jobs[pid]
        assert child.mode == "done" and not child.claimed
        child.claimed = True
        return child.result

    def step(self, pid, outcome=0):
        assert pid in self.enabled()
        job = self.jobs[pid]
        self.trace.append(("schedule", pid, job.mode))
        if job.mode == "left":
            child, kont = job.waiting
            result = self.claim(child)
            code = continuation(kont, result.value)
            child = self.allocate(code, result.value, job.rank + (1, 0), pid)
            job.mode = "join"
            job.waiting = {"kind": "bind", "left": result, "children": [child]}
            return
        if job.mode == "join":
            assert len(job.waiting["children"]) == 1
            right = self.claim(job.waiting["children"][0])
            left = job.waiting["left"]
            self.finish(pid, RuleResult(right.value, ("bind", left.raw, (right.raw,)),
                                        left.events + right.events))
            return
        kind, args = job.code.kind, job.code.args
        if kind == "bind":
            child = self.allocate(args[0], job.value, job.rank + (0,), pid)
            job.mode, job.waiting = "left", (child, args[1])
        elif kind == "spawn":
            fresh = self.next_job
            child = self.allocate(args[0], args[1](job.value), (fresh,), None)
            self.finish(pid, RuleResult(child, ("spawn", child)))
        elif kind == "call":
            name, argument = args
            value = argument(job.value)
            job.code, job.value = procedure(name, value), value
            self.trace.append(("unfold", pid, name))
        elif kind == "send":
            channel, payload_function = args
            payload = deepcopy(payload_function(job.value))
            mid = self.next_message
            self.next_message += 1
            self.messages[mid] = (channel, payload)
            self.queues.setdefault(channel, []).append(mid)
            self.finish(pid, RuleResult(mid, ("send", mid)))
        elif kind == "receive":
            channel = args[0]
            mid = self.queues[channel][0]
            self.queues[channel] = self.queues[channel][1:]
            actual_channel, payload = self.messages.pop(mid)
            assert actual_channel == channel
            self.finish(pid, RuleResult(payload, ("receive", mid)))
        elif kind == "ret":
            self.finish(pid, RuleResult(args[0](job.value), ("ret",)))
        else:
            assert kind == "op"
            name, argument_function = args
            argument = argument_function(job.value)
            # These formulas are independent of the runtime primitive callbacks.
            n = argument if name == "read" else argument[0]
            assert n == self.world["commits"]
            if name == "read":
                value = (n, self.world["x"])
            elif name == "flip":
                self.world["x"] ^= 1
                value = (n, self.world["x"])
            else:
                assert name == "commit" and argument[2][0] == n
                assert argument[2][1] in (0, 1)
                self.world["x"] = 1 - argument[1]
                self.world["commits"] += 1
                value = self.world["commits"]
            if self.source:
                self.world["aux"] = outcome
                weight, witness = self.weights[outcome], f"{name}:aux{outcome}"
            else:
                assert outcome == 0
                weight, witness = F(1), f"{name}:unit"
            event_id = len(self.events)
            self.events.append(dict(pid=pid, name=name, witness=witness, weight=weight,
                                    cost=(1,), event=name))
            self.finish(pid, RuleResult(value, ("op", name, 0, outcome, witness), (event_id,)))


def freeze(value):
    if isinstance(value, dict):
        return tuple((key, freeze(item)) for key, item in sorted(value.items()))
    if isinstance(value, (tuple, list)):
        return tuple(freeze(item) for item in value)
    return value


def raw_image(raw):
    if raw[0] == "op":
        return "op", raw[1], raw[2], 0, f"{raw[1]}:unit"
    if raw[0] == "bind":
        return "bind", raw_image(raw[1]), tuple(raw_image(child) for child in raw[2])
    assert raw[0] in ("ret", "send", "receive", "spawn")
    return raw


def snapshot(runtime, machine, *, independent=False, mapped=False):
    """Full state of the admitted fragment, retaining every allocated job."""
    def result_view(result):
        if result is None:
            return None
        if independent:
            value = result.value
        else:
            assert isinstance(result.tree, runtime.Leaf) and result.tree.caps == ()
            value = result.tree.value
        raw = raw_image(result.raw) if mapped else result.raw
        return ("leaf", freeze(value), ()), freeze(raw), result.events, result.status

    job_views = []
    for pid, job in sorted(machine.jobs.items()):
        code = job.code if independent else decode_code(runtime, job.term)
        waiting = job.waiting
        if waiting is not None:
            if isinstance(waiting, tuple):
                kont = waiting[1] if independent else waiting[1].descriptor
                waiting = "left", waiting[0], kont
            else:
                assert waiting["kind"] == "bind" and len(waiting["children"]) == 1
                waiting = "join", result_view(waiting["left"]), tuple(waiting["children"])
        job_views.append((pid, code, freeze(job.value), job.rank, job.mode, waiting,
                          result_view(job.result), job.parent, job.claimed))
    world = {key: value for key, value in machine.world.items() if not mapped or key != "aux"}
    events = []
    for event in machine.events:
        event = dict(event)
        if mapped:
            # This maps annotations to the selected target row. Probability
            # correctness is proved by fibre summation, not pointwise equality.
            event["witness"] = f"{event['name']}:unit"
            event["weight"] = F(1)
        events.append(freeze(event))
    if independent:
        authority = (), (), ()
    else:
        assert machine.ledger == machine.kinds == machine.stores == {}
        authority = freeze(machine.ledger), freeze(machine.kinds), freeze(machine.stores)
    return (tuple(job_views), freeze(world), freeze(machine.messages), freeze(machine.queues),
            tuple(events), tuple(machine.trace), machine.next_job, machine.next_message, authority)


def select(machine, policy, previous):
    ready = machine.enabled()
    assert ready, "A premature deadlock is a failure, not a completed epoch."
    if policy == "min_rank":
        return min(ready, key=lambda pid: machine.jobs[pid].rank)
    if policy == "max_rank":
        return max(ready, key=lambda pid: machine.jobs[pid].rank)
    assert policy == "round_robin"
    after = [pid for pid in ready if pid > previous]
    return min(after or ready)


def is_primitive(runtime, machine, pid):
    job = machine.jobs[pid]
    return job.mode == "eval" and isinstance(job.term, runtime.Op)


def completed_two_epochs(machine):
    # Observe after the next client recursive unfolding, before its third read.
    # Pending ancestors/results/queues are retained; this is not termination.
    unfolds = sum(item[0] == "unfold" and item[2] == "client" for item in machine.trace)
    return machine.world["commits"] == 2 and unfolds == 3


def collect_boundaries(runtime, machine, counts):
    ready = set(machine.enabled())
    for pid, job in machine.jobs.items():
        if job.mode == "eval" and isinstance(job.term, runtime.Receive):
            channel = job.term.channel
            if not machine.queues.get(channel):
                assert pid not in ready
                counts[f"suspended_{channel}_observations"] += 1
    counts["pending_message_observations"] += int(bool(machine.messages))
    counts["max_allocated_jobs"] = max(counts["max_allocated_jobs"], len(machine.jobs))
    counts["retained_waiting_ancestor_observations"] += int(any(j.mode == "join" for j in machine.jobs.values()))


def target_execution(runtime, policy, counts):
    target = runtime_machine(runtime, False, (F(1),))
    rules = RestrictedRules(False, (F(1),))
    states = [snapshot(runtime, target)]
    assert states[0] == snapshot(runtime, rules, independent=True)
    pids, primitives = [], []
    previous = -1
    for _ in range(500):
        if completed_two_epochs(target):
            break
        collect_boundaries(runtime, target, counts)
        assert target.enabled() == rules.enabled()
        pid = select(target, policy, previous)
        assert pid == select(rules, policy, previous)
        job = target.jobs[pid]
        rule_name = job.mode if job.mode in ("left", "join") else decode_code(runtime, job.term).kind
        counts["rule_" + rule_name] += 1
        primitives.append(is_primitive(runtime, target, pid))
        pids.append(pid)
        target.step(pid, message=0)
        rules.step(pid)
        actual = snapshot(runtime, target)
        assert actual == snapshot(runtime, rules, independent=True)
        if primitives[-1] and target.events[-1]["name"] == "commit":
            assert target.world["x"] == target.world["commits"] % 2
            if target.world["commits"] == 1:
                # Actual worker flip and stale client commit both leave 1;
                # independently, two serial flips from 0 leave 0.
                assert target.world["x"] == 1
                serial_bit = 0
                for _ in range(2):
                    serial_bit ^= 1
                assert serial_bit == 0 != target.world["x"]
        states.append(actual)
        previous = pid
    else:
        raise AssertionError("Finite observation bound reached before the specified two epochs.")
    assert completed_two_epochs(target) and target.jobs[0].mode != "done"
    assert sum(primitives) == len(target.events) == 6
    assert target.word == ("read", "flip", "commit") * 2
    assert target.world == {"x": 0, "commits": 2}
    assert target.weight == 1 and target.cost == (6,)
    assert sum(item[0] == "unfold" and item[2] == "server" for item in target.trace) >= 2
    return states, pids, primitives, target


def protocol_checks(runtime):
    counts = defaultdict(int)
    policies = ("min_rank", "max_rank", "round_robin")
    step_counts = {}
    weights_cases = {"fair": (F(1, 2), F(1, 2)), "zero_raw": (F(1), F(0))}
    traces = []
    for policy in policies:
        target_states, pids, primitive_flags, target = target_execution(runtime, policy, counts)
        traces.append(tuple(target.trace))
        step_counts[policy] = len(pids)
        for case, weights in weights_cases.items():
            assert sum(weights) == 1
            pushed_masses = [F(0) for _ in target_states]
            raw_prefixes = [set() for _ in target_states]
            for choices in product((0, 1), repeat=6):
                source = runtime_machine(runtime, True, weights)
                rules = RestrictedRules(True, weights)
                used = []
                full_mass = F(1)
                for choice in choices:
                    full_mass *= weights[choice]
                previous = -1
                for step in range(len(target_states)):
                    # Independent operational interpretation at every boundary.
                    assert snapshot(runtime, source) == snapshot(runtime, rules, independent=True)
                    # Actual directed history map, including every admin step.
                    assert snapshot(runtime, source, mapped=True) == target_states[step]
                    pushed_masses[step] += full_mass
                    raw_prefixes[step].add(tuple(used))
                    counts["source_boundary_comparisons"] += 1
                    if step == len(pids):
                        break
                    assert source.enabled() == rules.enabled()
                    pid = select(source, policy, previous)
                    assert pid == pids[step] == select(rules, policy, previous)
                    flag = is_primitive(runtime, source, pid)
                    assert flag == primitive_flags[step]
                    outcome = choices[len(used)] if flag else 0
                    if flag:
                        used.append(outcome)
                    source.step(pid, outcome=outcome, message=0)
                    rules.step(pid, outcome=outcome)
                    previous = pid
                assert tuple(used) == choices and completed_two_epochs(source)
                assert source.weight == full_mass
                assert source.cost == target.cost and source.word == target.word
                counts["source_complete_raw_paths"] += 1
                counts["source_zero_weight_complete_paths"] += int(full_mass == 0)
            assert all(mass == 1 for mass in pushed_masses)
            for step, seen in enumerate(raw_prefixes):
                consumed = sum(primitive_flags[:step])
                assert seen == set(product((0, 1), repeat=consumed))
                counts["exact_prefix_fibre_mass_checks"] += 1
                if step:
                    previous_seen = {prefix[:-1] if primitive_flags[step - 1] else prefix for prefix in seen}
                    assert previous_seen == raw_prefixes[step - 1]
                    counts["raw_prefix_truncation_checks"] += 1
            counts["policy_and_probability_families"] += 1
    assert len(set(traces)) == len(policies)
    assert counts["source_complete_raw_paths"] == 3 * 2 * 64
    assert counts["source_zero_weight_complete_paths"] == 3 * 63
    assert counts["suspended_ack_observations"] and counts["suspended_req_observations"]
    assert counts["pending_message_observations"]
    assert counts["retained_waiting_ancestor_observations"]
    return {**dict(counts), "actual_runtime_steps_by_policy": step_counts,
            "policies": list(policies), "weight_families": {name: [str(x) for x in w] for name, w in weights_cases.items()},
            "primitive_word": ["read", "flip", "commit"] * 2,
            "observation_boundary": "After two commits and the third client Call unfolding, before the third read; root and recursive ancestors remain unfinished.",
            "shared_state_separator": "Each epoch maps x to 1-x: the worker flips current x, then the client overwrites with 1-cached_read. Two serialized flips would map x to x.",
            "native_grade_scope": "Terminal context/content coefficients; directed raw primitive maps and full state/body comparisons retained."}


def fifo_check(runtime):
    actual = runtime_machine(runtime, False, (F(1),), fifo=True)
    rules = RestrictedRules(False, (F(1),), fifo=True)
    previous = -1
    saw_two = False
    received = []
    spawn_id = None
    steps = 0
    rule_coverage = defaultdict(int)
    for _ in range(100):
        assert snapshot(runtime, actual) == snapshot(runtime, rules, independent=True)
        assert actual.enabled() == rules.enabled()
        if not actual.enabled():
            break
        if actual.queues.get("fifo") == [0, 1]:
            saw_two = True
        pid = select(actual, "min_rank", previous)
        assert pid == select(rules, "min_rank", previous)
        job = actual.jobs[pid]
        rule_name = job.mode if job.mode in ("left", "join") else decode_code(runtime, job.term).kind
        rule_coverage[rule_name] += 1
        receiving = job.mode == "eval" and isinstance(job.term, runtime.Receive)
        spawning = job.mode == "eval" and isinstance(job.term, runtime.Spawn)
        expected_mid = actual.queues["fifo"][0] if receiving else None
        actual.step(pid, message=0)
        rules.step(pid)
        if spawning:
            spawn_id = actual.jobs[pid].result.tree.value
        if receiving:
            result = actual.jobs[pid].result
            assert result.raw == ("receive", expected_mid)
            received.append((expected_mid, result.tree.value))
        previous = pid
        steps += 1
    else:
        raise AssertionError("FIFO fixture did not complete.")
    assert snapshot(runtime, actual) == snapshot(runtime, rules, independent=True)
    assert saw_two and received == [(0, "first"), (1, "second")]
    assert actual.jobs[0].mode == actual.jobs[spawn_id].mode == "done"
    assert actual.jobs[spawn_id].result.tree.value == ("first", "second")
    assert not actual.messages and actual.queues == {"fifo": []}
    assert actual.next_message == 2
    assert set(rule_coverage) == {"bind", "spawn", "left", "call", "send", "receive", "ret", "join"}
    return {"runtime_steps": steps, "two_messages_simultaneously_queued": saw_two,
            "received_message_ids_and_payloads": received,
            "independently_checked_rule_coverage": dict(rule_coverage),
            "scope": "The selected interpretation passes message=0. The general runtime permits other queue indices."}


def status_and_environment_checks(runtime):
    blocked = runtime_machine(runtime, False, (F(1),), code=receive("absent"))
    blocked_rules = RestrictedRules(False, (F(1),), code=receive("absent"))
    before = snapshot(runtime, blocked)
    assert before == snapshot(runtime, blocked_rules, independent=True)
    assert blocked.enabled() == blocked_rules.enabled() == []
    blocked.prefix(8)
    assert snapshot(runtime, blocked) == before and blocked.jobs[0].mode == "eval"
    assert blocked.jobs[0].result is None and not blocked.trace and not blocked.events

    returned = runtime_machine(runtime, False, (F(1),), code=Code("ret", (ID,)))
    returned_rules = RestrictedRules(False, (F(1),), code=Code("ret", (ID,)))
    returned.step(0)
    returned_rules.step(0)
    assert snapshot(runtime, returned) == snapshot(runtime, returned_rules, independent=True)
    assert returned.enabled() == [] and returned.jobs[0].mode == "done"
    assert returned.jobs[0].result is not None

    spin = runtime_machine(runtime, False, (F(1),), code=call("spin"))
    spin_rules = RestrictedRules(False, (F(1),), code=call("spin"))
    for _ in range(8):
        assert spin.enabled() == spin_rules.enabled() == [0]
        spin.step(0)
        spin_rules.step(0)
        assert snapshot(runtime, spin) == snapshot(runtime, spin_rules, independent=True)
    assert spin.jobs[0].mode == "eval" and spin.jobs[0].result is None
    assert len(spin.trace) == 16 and not spin.events

    source = runtime_machine(runtime, True, (F(1, 2), F(1, 2)))
    target = runtime_machine(runtime, False, (F(1),))
    source_rules = RestrictedRules(True, (F(1, 2), F(1, 2)))
    target_rules = RestrictedRules(False, (F(1),))
    previous = -1
    for _ in range(100):
        if any(j.mode == "eval" and isinstance(j.term, runtime.Receive)
               and j.term.channel == "ack" and not source.queues.get("ack")
               for j in source.jobs.values()):
            break
        pid = select(source, "min_rank", previous)
        assert pid == select(target, "min_rank", previous)
        source.step(pid, outcome=0, message=0)
        target.step(pid, message=0)
        source_rules.step(pid, outcome=0)
        target_rules.step(pid)
        assert snapshot(runtime, source) == snapshot(runtime, source_rules, independent=True)
        assert snapshot(runtime, target) == snapshot(runtime, target_rules, independent=True)
        assert snapshot(runtime, source, mapped=True) == snapshot(runtime, target)
        previous = pid
    else:
        raise AssertionError("No actual suspended acknowledgment boundary found.")
    queue_before = deepcopy(source.queues), deepcopy(source.messages)
    for actual, rules in ((source, source_rules), (target, target_rules)):
        actual.environment_step("public-world-flip", lambda world: {**world, "x": 1 - world["x"]})
        rules.world["x"] ^= 1
        rules.trace.append(("environment", "public-world-flip"))
        assert snapshot(runtime, actual) == snapshot(runtime, rules, independent=True)
    assert snapshot(runtime, source, mapped=True) == snapshot(runtime, target)
    assert queue_before == (source.queues, source.messages)
    assert source.enabled() == target.enabled() == source_rules.enabled() == target_rules.enabled()
    return {"blocked_receive_adds_no_physical_or_padding_steps": True,
            "returned_and_suspended_statuses_distinct": True,
            "self_call_prefix_steps": 8,
            "self_call_administrative_trace_records": 16,
            "self_call_remains_enabled_without_result": True,
            "world_only_environment_flip_at_suspension_commutes_with_aux_erasure": True,
            "environment_leaves_messages_queues_and_guards_unchanged": True,
            "scope": "The self-call test inspects a finite prefix; the recursive rule permits further unfolding. No idle loop or status padding is added to physical execution."}


def load_runtime(path):
    spec = importlib.util.spec_from_file_location("checked_occurrence_runtime", path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def main():
    if not __debug__:
        raise RuntimeError("Run without optimization; assertions perform the diagnostics.")
    parser = argparse.ArgumentParser()
    default = Path(__file__).resolve().parents[3] / "feedback-and-concurrency" / "recursive-occurrence-machine" / "runtime" / "occurrence_machine.py"
    parser.add_argument("--runtime", type=Path, default=default)
    args = parser.parse_args()
    if not args.runtime.is_file():
        parser.error("runtime not found; supply --runtime PATH when running outside the repository check directory")
    runtime = load_runtime(args.runtime)
    result = {
        "status": "PASS",
        "runtime": str(args.runtime.resolve()),
        "protocol": protocol_checks(runtime),
        "fifo_fixture": fifo_check(runtime),
        "status_and_environment_fixtures": status_and_environment_checks(runtime),
        "preserved_state": "All allocated job IDs, code/continuation descriptors, values, ranks, modes, waiting records, result trees, mapped raw IDs, event IDs, claim flags, queue order, messages, allocation counters and administrative traces.",
        "comparison_boundary": "Primitive outcome index/witness and hidden world aux are erased. Event-row weights are mapped to the target row; probability correctness is exact fibre summation, not pointwise equality.",
        "scope": "Finite actual-runtime diagnostics for Spawn, unary Bind, Call, Op, Send, FIFO Receive and Ret with empty token bundles. Shared pure syntax/continuation definitions are trusted inputs. No full occurrence-language bridge, general callback validation, arbitrary scheduler theorem or physical resource/progress claim.",
    }
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
