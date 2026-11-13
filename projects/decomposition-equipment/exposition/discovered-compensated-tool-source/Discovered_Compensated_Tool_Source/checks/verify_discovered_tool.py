#!/usr/bin/env python3
"""Independent finite checks; finite evidence, not a proof of all dimensions.

Uses exhaustive possible worlds as the reference oracle. No author checker or
proof implementation is imported. Python's removable assert is never used.
"""
import argparse
import hashlib
import itertools
import json
from pathlib import Path


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def dot(x, y):
    return (x & y).bit_count() % 2


def close_span(rows):
    values = {0}
    for r in rows:
        values |= {x ^ r for x in tuple(values)}
    return frozenset(values)


def all_subspaces(m):
    known = {frozenset({0})}
    frontier = [frozenset({0})]
    while frontier:
        w = frontier.pop()
        for r in range(1 << m):
            if r not in w:
                new = frozenset(set(w) | {x ^ r for x in w})
                if new not in known:
                    known.add(new)
                    frontier.append(new)
    return sorted(known, key=lambda w: (len(w), tuple(sorted(w))))


def basis_of(w):
    basis = []
    generated = {0}
    for r in sorted(w):
        if r not in generated:
            basis.append(r)
            generated |= {x ^ r for x in tuple(generated)}
    require(generated == set(w), 'basis does not generate subspace')
    return tuple(basis)


def compatible(m, rows, bits):
    return tuple(theta for theta in range(1 << m)
                 if all(dot(theta, r) == b for r, b in zip(rows, bits)))


def certificate(rows, bits, v):
    for selection in itertools.product((0, 1), repeat=len(rows)):
        produced = correction = 0
        for use, row, bit in zip(selection, rows, bits):
            if use:
                produced ^= row
                correction ^= bit
        if produced == v:
            return tuple(selection), correction
    return None


def check_algebra(max_m):
    summary = []
    for m in range(1, max_m + 1):
        spaces = all_subspaces(m)
        fibre_count = activity_count = certificate_count = 0
        dependent_cases = inconsistent_cases = 0
        for w in spaces:
            rows = basis_of(w)
            data = {tuple(dot(theta, row) for row in rows)
                    for theta in range(1 << m)}
            for bits in sorted(data):
                worlds = compatible(m, rows, bits)
                require(bool(worlds), 'consistent evidence lost all worlds')
                fibre_count += 1
                for v in range(1 << m):
                    reference_values = {dot(theta, v) for theta in worlds}
                    cert = certificate(rows, bits, v)
                    require((len(reference_values) == 1) == (v in w),
                            f'rowspace criterion mismatch m={m}')
                    require((cert is not None) == (len(reference_values) == 1),
                            'certificate does not coincide with concrete uniformity')
                    if cert is not None:
                        certificate_count += 1
                        correction = cert[1]
                        require(reference_values == {correction}, 'wrong correction')
                        for desired in (0, 1):
                            command = desired ^ correction
                            require(all((command ^ dot(theta, v)) == desired
                                        for theta in worlds), 'release not uniformly correct')
                    else:
                        # Each proposed command fails in an actual compatible world.
                        for desired, command in itertools.product((0, 1), repeat=2):
                            require(any((command ^ dot(theta, v)) != desired
                                        for theta in worlds), 'uncertainty obstruction failed')
                    activity_count += 1
                # Repeated/redundant measured relations preserve the full fibre.
                extras = (0,) + rows + ((rows[0] ^ rows[-1],) if rows else ())
                extra_bits = tuple(dot(worlds[0], r) for r in extras)
                require(compatible(m, rows + extras, bits + extra_bits) == worlds,
                        'redundant evidence changes world fibre')
                dependent_cases += 1
                # Contradictory evidence must not be certified vacuously.
                bad_rows = rows + (0,)
                bad_bits = bits + (1,)
                require(compatible(m, bad_rows, bad_bits) == (),
                        'contradictory evidence accepted')
                inconsistent_cases += 1
        summary.append(dict(dimension=m, subspaces=len(spaces),
                            nonempty_affine_fibres=fibre_count,
                            activity_fibre_cases=activity_count,
                            certified_activity_cases=certificate_count,
                            dependent_evidence_cases=dependent_cases,
                            inconsistent_evidence_cases=inconsistent_cases))
    return summary


def check_joint_and_retraction():
    m, rows, bits = 2, (3,), (0,)
    worlds = compatible(m, rows, bits)
    require(worlds == (0, 3), 'expected correlated fibre')
    joint = {(dot(t, 1), dot(t, 2)) for t in worlds}
    independent = set(itertools.product({x for x, _ in joint}, {y for _, y in joint}))
    require(joint == {(0, 0), (1, 1)}, 'joint witness incorrect')
    require({x ^ y for x, y in joint} == {0}, 'joint guarantee missing')
    require({x ^ y for x, y in independent} == {0, 1}, 'marginal relaxation did not lose guarantee')
    require(certificate(rows, bits, 3)[1] == 0, 'paired activity uncertified')
    require(certificate(rows, bits, 1) is None, 'interrupted pair wrongly certified')
    require(certificate((), (), 3) is None, 'retracted evidence still authorizes pair')
    # More valid evidence may authorize an earlier prefix, but the cost of obtaining
    # it is a separate protocol obligation, not supplied by this algebra.
    require(certificate((3, 1), (0, 1), 1)[1] == 1, 'valid refinement not usable')
    # A zero-weight compatible world remains a declared possibility. A Dirac law
    # alone cannot justify universal correctness on that declared may set.
    prior = {0: 1, 3: 0}
    v, command, desired = 1, 0, 0
    law_failure = sum(weight for t, weight in prior.items()
                      if command ^ dot(t, v) != desired)
    may_failure = {t for t in worlds if command ^ dot(t, v) != desired}
    require(law_failure == 0 and may_failure == {3}, 'zero-weight boundary absent')
    return dict(worlds=list(worlds), joint_records=sorted(joint),
                independent_records=sorted(independent),
                certified_pair_correction=0, interrupted_prefix='UNRESOLVED',
                retracted_pair='UNRESOLVED',
                zero_weight_failure_worlds=sorted(may_failure))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--max-dimension', type=int, default=5)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = dict(status='PASS', finite_scope='All affine evidence fibres and activities through stated dimensions; not an unrestricted proof',
                  algebra=check_algebra(args.max_dimension),
                  joint_and_retraction=check_joint_and_retraction())
    rendered = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.output:
        args.output.write_text(rendered)
    print(rendered, end='')

if __name__ == '__main__':
    main()
