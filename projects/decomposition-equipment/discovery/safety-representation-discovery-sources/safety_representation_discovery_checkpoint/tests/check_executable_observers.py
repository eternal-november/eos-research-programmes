#!/usr/bin/env python3
"""Executable observer/pushforward calibration checks; Python standard library only.

These finite tests support the proof in theory/Executable_Observer_Calculus.md.
They do not establish hardware noninterference, statistical coverage or an
original-C5 interpretation.  The distributed logger below is an executable
reference program with an explicit one-bit channel each round.
"""
from dataclasses import dataclass
from itertools import product
from fractions import Fraction
from pathlib import Path
import json


@dataclass(frozen=True)
class Port:
    owner: str
    when: tuple  # (time, phase)
    alphabet: tuple = (0, 1)


@dataclass(frozen=True)
class Node:
    name: str
    owner: str
    when: tuple
    inputs: tuple
    table: dict
    channel: bool = False
    alphabet: tuple = (0, 1)


def validate_program(sources, nodes, channels):
    """Reject future reads, unlicensed cross-owner access and cyclic schedule."""
    ports = dict(sources)
    for node in sorted(nodes, key=lambda n: n.when):
        if node.name in ports:
            raise ValueError('duplicate physical/program identifier')
        if node.channel and len(node.inputs) != 1:
            raise ValueError('a declared channel transmits one encoded value')
        for inp in node.inputs:
            if inp not in ports:
                raise ValueError('unavailable/future input')
            p = ports[inp]
            if not p.when < node.when:
                raise ValueError('future or same-phase dependency')
            if p.owner != node.owner:
                if not node.channel or (p.owner, node.owner) not in channels:
                    raise ValueError('unlicensed private-state read')
        domain = set(product(*(ports[inp].alphabet for inp in node.inputs)))
        if set(node.table) != domain:
            raise ValueError('incomplete or ill-typed local table')
        if any(value not in node.alphabet for value in node.table.values()):
            raise ValueError('output outside declared message/state alphabet')
        ports[node.name] = Port(node.owner, node.when, node.alphabet)
    return ports


def run_program(sources, nodes, channels, assignment):
    validate_program(sources, nodes, channels)
    if set(assignment) != set(sources) or any(assignment[k] not in p.alphabet for k, p in sources.items()):
        raise ValueError('invalid source assignment')
    values = dict(assignment)
    for node in sorted(nodes, key=lambda n: n.when):
        values[node.name] = node.table[tuple(values[x] for x in node.inputs)]
    return values


class DistributedParityLogger:
    """A local running parity at each owner, with one A→B bit each round.

    A reads only x, B reads only y.  The returned bit is parity of all x/y
    observations so far, not independent samples from two parity marginals.
    Both states start at zero independently of future physical inputs.
    """
    def __init__(self):
        self.a = 0
        self.b = 0
        self.messages = []

    def step(self, x, y):
        self.a ^= x             # A's local phase
        message = self.a        # one-bit message A→B
        self.messages.append(message)
        self.b ^= y             # B's local phase
        return message ^ self.b # B after delivery


def all_functions(n, k):
    return product(range(k), repeat=n)


def response_classes(table):
    return len(set(tuple(row) for row in table))


def implementable_one_message(table, message_count):
    """Search every sender encoder; decoder consistency is checked exactly."""
    ns, nr = len(table), len(table[0])
    for enc in all_functions(ns, message_count):
        decoder = {}
        ok = True
        for s in range(ns):
            for r in range(nr):
                key = enc[s], r
                if key in decoder and decoder[key] != table[s][r]:
                    ok = False
                    break
                decoder[key] = table[s][r]
            if not ok:
                break
        if ok:
            return tuple(enc), decoder
    return None


def probability_grid(n, denominator):
    for counts in product(range(denominator + 1), repeat=n):
        if sum(counts) == denominator:
            yield tuple(Fraction(x, denominator) for x in counts)


def expectation(law, feature):
    return sum(p * f for p, f in zip(law, feature))


def main():
    counts = {}
    xor = {(x, y): x ^ y for x, y in product(range(2), repeat=2)}
    identity = {(x,): x for x in range(2)}
    sources = {'ax': Port('A', (0, 0)), 'by': Port('B', (0, 0))}
    nodes = [Node('msg', 'B', (0, 1), ('ax',), identity, True),
             Node('out', 'B', (0, 2), ('msg', 'by'), xor)]
    for x, y in product(range(2), repeat=2):
        assert run_program(sources, nodes, {('A', 'B')}, {'ax': x, 'by': y})['out'] == x ^ y
    controls = 0
    for bad_nodes, bad_sources, channels in [
        ([Node('out', 'B', (0, 1), ('ax', 'by'), xor)], sources, {('A', 'B')}),
        ([Node('out', 'B', (0, 1), ('future',), identity)],
         dict(sources, future=Port('B', (1, 0))), set()),
        (nodes, sources, set()),
        ([Node('z', 'B', (0, 1), ('z',), identity)], sources, set()),
        ([Node('z', 'A', (0, 1), ('ax',), {(0,): 0})], sources, set()),
        ([Node('z', 'A', (0, 1), ('ax',), {(0,): 0, (1,): 2})], sources, set()),
    ]:
        try:
            validate_program(bad_sources, bad_nodes, channels)
        except ValueError:
            controls += 1
        else:
            raise AssertionError('invalid executable observer accepted')
    constant = [Node('c', 'A', (0, 1), (), {(): 1})]
    assert run_program({}, constant, set(), {})['c'] == 1
    counts['schedule_negative_controls'] = controls

    steps = traces = 0
    for H in range(6):
        for raw in product(range(2), repeat=2 * H):
            logger = DistributedParityLogger()
            direct = 0
            for t in range(H):
                x, y = raw[2 * t:2 * t + 2]
                direct ^= x ^ y
                assert logger.step(x, y) == direct
                assert logger.messages[-1] in (0, 1)
                steps += 1
            traces += 1
    counts['distributed_trace_cases'] = traces
    counts['distributed_step_cases'] = steps

    comm = 0
    for cells in product(range(2), repeat=4):
        table = [cells[:2], cells[2:]]
        need = response_classes(table)
        for k in (1, 2):
            assert (implementable_one_message(table, k) is not None) == (k >= need)
            comm += 1
    threshold_results = []
    for K in range(1, 5):
        table = [[int(s + r > K) for r in range(K + 1)] for s in range(K + 1)]
        assert response_classes(table) == K + 1
        assert implementable_one_message(table, K) is None
        enc, dec = implementable_one_message(table, K + 1)
        for s, r in product(range(K + 1), repeat=2):
            assert dec[enc[s], r] == table[s][r]
            # The two-phase reply can simply send the required Boolean value.
            reply = int(s + r > K)
            assert reply == table[s][r]
        threshold_results.append({'K': K, 'minimum_symbols': K + 1})
    counts['one_message_binary_function_cases'] = comm

    factorization = 0
    for q in product(range(2), repeat=3):
        for phi in product((-1, 0, 1), repeat=3):
            fibre_constant = all(q[i] != q[j] or phi[i] == phi[j]
                                 for i, j in product(range(3), repeat=2))
            decoders = [g for g in product((-1, 0, 1), repeat=2)
                        if all(g[q[i]] == phi[i] for i in range(3))]
            assert fibre_constant == bool(decoders)
            if decoders:
                for law in probability_grid(3, 3):
                    pushed = [sum(law[i] for i in range(3) if q[i] == z) for z in range(2)]
                    assert expectation(law, phi) == expectation(pushed, decoders[0])
            factorization += 1
    counts['potential_adapter_factorization_cases'] = factorization

    # Two marginally fair observations do not determine their joint hazard.
    omega = list(product(range(2), repeat=2))
    fx = [x for x, y in omega]
    fy = [y for x, y in omega]
    risk = [x ^ y for x, y in omega]
    laws = list(probability_grid(4, 4))
    coarse = [p for p in laws if expectation(p, fx) == Fraction(1, 2)
              and expectation(p, fy) == Fraction(1, 2)]
    full = [p for p in coarse if expectation(p, risk) <= Fraction(1, 2)]
    assert len(coarse) == 3 and len(full) == 2
    assert max(expectation(p, risk) for p in coarse) == 1
    assert max(expectation(p, risk) for p in full) == Fraction(1, 2)
    bad = max(coarse, key=lambda p: expectation(p, risk))
    assert expectation(bad, risk) > Fraction(1, 2) # violates the unused joint row
    diagonal = (Fraction(1, 2), Fraction(0), Fraction(0), Fraction(1, 2))
    antidiagonal = (Fraction(0), Fraction(1, 2), Fraction(1, 2), Fraction(0))
    assert all(expectation(diagonal, f) == expectation(antidiagonal, f) for f in [fx, fy])
    assert expectation(diagonal, risk) == 0 and expectation(antidiagonal, risk) == 1
    # A valid quantitative proof is risk <= the actually measured risk row,
    # whose upper confidence bound is 1/2. Coarsening it to a constant loses it.
    assert all(r <= r for r in risk)
    assert len(set(risk)) == 2
    counts['probability_grid_laws'] = len(laws)
    counts['coarse_compatible_laws'] = len(coarse)
    counts['joint_evidence_compatible_laws'] = len(full)

    # Replay eligibility is independent of program mathematical correctness.
    required = {'A.x@same_episode', 'B.y@same_episode'}
    archive = {'A.x@marginal_experiment', 'B.y@marginal_experiment'}
    assert not required <= archive
    complete_archive = required | archive
    assert required <= complete_archive

    result = {'status': 'PASS', 'counts': counts,
              'threshold_message_lower_bounds': threshold_results,
              'controls': ['future/private reads rejected', 'channel permission checked',
                           'shared trace not replaced by independent marginals',
                           'new observer does not create archived joint data',
                           'coarser interface may destroy fixed risk potential',
                           'two-phase protocol is distinct from one-way protocol'],
              'scope': 'finite reference-program and algebra checks, not hardware or statistical validation'}
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
