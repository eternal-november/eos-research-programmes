"""Source/effect refinement checks; no full physical-source admission claim."""
from __future__ import annotations
import argparse
import copy
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations, product
import json
import sys
from pathlib import Path
import program_model as P
import incidence_model as I

HERE = Path(__file__).resolve().parent


def require(ok, message):
    if not ok:
        raise AssertionError(message)


def reachable(edges, start):
    seen = {start}
    while True:
        more = {b for a, b in edges if a in seen}
        if more <= seen:
            return seen
        seen |= more


def fault_closure(edges, zones, selected):
    out = set(edges)
    for z in selected:
        out.update(product(zones[z], repeat=2))
    return out


def graph_checks():
    # Parameterized discrete fibre family, not a spatial/mechanical realization.
    # An allowed damage region may change any edge among its named terminals.
    checks = 0
    deletion_checks = 0
    for lanes in (2, 3, 5):
        edges = set()
        zones = []
        for lane in range(lanes):
            path = tuple((lane, stage) for stage in range(5))
            edges.update(zip(path, path[1:]))
            zones.extend((path[1:3], path[2:5]))
        for count in range(min(3, len(zones)) + 1):
            for chosen in combinations(range(len(zones)), count):
                upper = fault_closure(edges, zones, chosen)
                for lane in range(lanes):
                    actual = reachable(upper, (lane, 0))
                    ends = {node[0] for node in actual if node[1] == 4}
                    require(ends <= {lane}, 'Separated fibre acquired a wrong endpoint')
                    checks += 1
                    # Arbitrary deletion sampled exhaustively for every single edge.
                    for edge in upper:
                        require(reachable(upper - {edge}, (lane, 0)) <= actual,
                                'Deleting an edge increased reach')
                        deletion_checks += 1
    base = {(('A', j), ('A', j+1)) for j in range(4)}
    base |= {(('B', j), ('B', j+1)) for j in range(4)}
    bad_zones = {
        'shared_decoder': (('A', 1), ('B', 1)),
        'adjacent_endpoints': (('A', 4), ('B', 4)),
        'moved_mount': (('A', 3), ('B', 4)),
    }
    countergraphs = {}
    for name, terminals in bad_zones.items():
        expanded = fault_closure(base, [terminals], (0,))
        require(('B', 4) in reachable(expanded, ('A', 0)), name)
        countergraphs[name] = ['A', 'B']
    cam = set(base) | {('CAM', ('A', 2)), ('CAM', ('B', 2))}
    require(('B', 4) in reachable(cam, 'CAM'), 'Common cam-energy path lost')
    countergraphs['shared_cam_energy'] = ['A', 'B']
    return dict(separated_joint_patch_source_checks=checks,
                edge_deletion_checks=deletion_checks, rejected_countergraphs=countergraphs,
                scope='Graph conditional on complete terminals/edges, reachable geometry and separate actual effect-lifetime law')


def heterogeneous_envelopes():
    checks = 0
    # Current actual P guard margin .3; all reports already nominally clipped.
    for slow_sample, slow_error, slow_growth, fast_actual, fast_report in product(
            (F(0), F(1, 5), F(3, 5)), (F(-1, 100), F(0), F(1, 100)),
            (F(0), F(1, 10), F(1, 5)), (F(0), F(1, 10), F(1, 5)),
            (F(0), F(1, 100), F(1, 5))):
        report = max(F(0), slow_sample + slow_error)
        folded = max(report, fast_report)
        actual = max(slow_sample + slow_growth, fast_actual)
        if folded + F(3, 10) <= 1:
            require(actual <= folded + F(3, 10) <= 1,
                    'Mixed future-envelope fold was unsound')
        checks += 1
    # Fast pulses satisfy the peak but violate the slow source's slew bound.
    pulse_change = F(1, 5)
    pulse_dt = F(1, 1000)
    require(pulse_change > pulse_dt / 10000, 'Peak cap falsely became Lipschitz')
    return dict(mixed_member_cases=checks, fast_peak='1/5', guard_margin='3/10',
                pulse_obeys_peak_but_not_slow_slew=True,
                isolation_requires_separate_envelope=True)


def physical_counterexamples():
    good, contribution, stiction = 34, F(2), F(28)
    actual_load = {'A': F(1, 5), 'B': F(6, 5)}
    force = good * contribution
    require(actual_load['A'] <= 1 < actual_load['B'] and force > stiction,
            'Redirection witness lost')
    leakage = F(1, 1000) * 176
    require(0 < leakage and F(274, 10) + leakage < stiction,
            'Pressure/nonmovement distinction lost')
    # Finite elastic/fluid stored energy can support static contact pressure:
    # zero velocity means zero mechanical work; no fresh energy is required.
    def load(t):
        return min(F(6, 5), F(1, 5) + F(t, 10000))
    pressure = F(2)
    require(load(0) + F(3, 10) < 1 and load(5000) + F(3, 10) == 1,
            'Initial guard or last positive boundary changed')
    require(load(8000) == 1 < load(8001) and pressure < stiction,
            'Retained-pressure conduct counterexample lost')
    for a, b in zip(range(0, 10000, 100), range(100, 10100, 100)):
        require(load(b) - load(a) <= F(b-a, 10000), 'Load ramp exceeds raw slew')
    return dict(common_redirection=dict(intact_helpers=good, force=str(force),
                   intended_load=str(actual_load['A']), actual_load=str(actual_load['B'])),
                nonmovement_does_not_prove_conduct=dict(leakage=str(leakage),
                   total_with_hostile=str(F(274, 10)+leakage), stiction=str(stiction)),
                retained_pressure=dict(last_guard_boundary=5000, first_integer_violation=8001,
                   pressure=str(pressure), mechanical_work_while_static='0',
                   finite_spring_energy='1', spring_stiffness='2', spring_displacement='1',
                   scope='Refutes universal issuer-origin conduct or an unqualified nominal tail claim; independently faulty fields still owe global consequence accounting'))


def weighted_plant_checks():
    cases = 0
    upper = F(199, 300)
    lower = F(131, 300)
    service = F(3, 20)
    upper_margin = F(11, 2500)
    lower_margin = F(261, 2500)
    for m in range(72, 145, 2):
        for bad in range(7):
            for physical in range(min(1, bad)+1):
                weight = bad+3*physical
                u_up = (F(86,100)*(m-bad)-weight)/m
                u_low = (F(34,100)*(m-bad)+weight)/m
                u_service = (F(3,10)*(m-bad)-weight)/m
                collar_up = (F(84,100)*(m-bad)-weight)/m-F(6406,10000)
                collar_low = F(5594,10000)-(F(36,100)*(m-bad)+weight)/m
                require(u_up >= upper and u_low <= lower and u_service >= service,
                        'Weighted boundary/service envelope failed')
                require(collar_up >= upper_margin and collar_low >= lower_margin,
                        'Weighted inward collar failed')
                cases += 1
    require(service > F(1,10) and upper_margin > 0 and lower_margin > 0,
            'Strict plant margin lost')
    derivative = F(1658,1000)+F(3,72)
    rank_slew = 2*derivative
    require(rank_slew > F(3316,1000), 'Broader faulty blend reused old sample slope')
    initial_fallback_floor = (F(3,5)*66-9)/72
    require(initial_fallback_floor > F(1,10), 'Commissioning fallback loses flow')
    # Neither an actor nor its actual output changes identity just because an
    # output is illegal. The realization fault is declared in advance.
    targets = (0, 1, 2)
    persistent = {1}
    actual_pressure = {t: F(0) for t in targets}
    for issuer in range(34):
        requested_target, requested_side, requested_force = 1, 'A', F(2)
        # The local target router is allowed to combine into B, but no other
        # target acquires an unaccounted pressure edge in this signature.
        actual_pressure[requested_target] += requested_force
    require(actual_pressure == {0:F(0), 1:F(68), 2:F(0)}, 'Fixture envelope lost actual force')
    require(1 in persistent and actual_pressure[1] > F(274,10),
            'Faulty fixture was charged under intact-target W')
    # A newly allowed escape edge changes support; retaining one target would
    # be a false certificate even though the original physical fault count is1.
    escaped = {0:F(0), 1:F(0), 2:F(68)}
    require({t for t, force in escaped.items() if force > 0} - persistent == {2},
            'Wrong-target escape was hidden by original fault identity')
    return dict(checked_regional_parameter_cases=cases,
                bad_output_weight='b+3p (four unit bank/coordinate sources at each physically damaged fixture)',
                upper_boundary_flow_floor=str(upper), lower_boundary_flow_ceiling=str(lower),
                interior_service_floor=str(service), upper_collar_margin=str(upper_margin),
                lower_collar_margin=str(lower_margin), absolute_coordinate_derivative=str(derivative),
                rank_one_slew=str(rank_slew), commissioning_fallback_floor=str(initial_fallback_floor),
                persistent_fixture_actual_force='68', intact_target_adverse_bound='137/5',
                remote_escape_changes_support=True,
                scope='General interval-sum proof with conditional physical boundary; not a realization of the complete DefectStep')


def shared_switch_check():
    selected, _ = I.groups(0, 1, 432)
    require(selected == tuple(range(413, 426)), 'Wrong actual observer roster')
    reached = I.reached_slots(0, selected, {1})
    require(not reached, 'A target status fault was silently called a transport fault')
    compiled = P.compile_check(P.Design(origins=13))
    k = compiled.constants
    m = P.formation(compiled)
    ports = P.RawPorts(compiled)
    key = 3 + k['POWER_OFF_A']
    for origin in range(13):
        for bank in range(2):
            ports.fast[(origin, bank, key)] = 1
    m.enter('contact', (0, k['POWER_OFF_A']))
    m.run(ports, until_yield=False)
    require(m.result() == 1, 'Actual shared-switch acceptance witness lost')
    return dict(observer_hosts=list(selected), corrupted_transport_slots=[],
                reported_switch=1, actual_no_new_launch=False, executed_contact_result=1)


def shared_target_status_probe():
    compiled = P.compile_check(P.Design(origins=13))
    k = compiled.constants
    formed = P.formation(compiled)
    cases = 0
    actions = set()
    maxsteps = 0
    for half in range(2):
        for phase in range(k['PHASES']):
            for abort in (False, True):
                m = copy.deepcopy(formed)
                ports = P.RawPorts(compiled)
                view = P.populated_view(compiled, half, phase, 0)
                for j in range(k['POSE_WORDS'], len(view)):
                    view[j] = 1
                view[k['MODE']] = 0
                view[k['ABORT_FULL']] = int(abort)
                view[k['ANCHOR_IS_A']] = int(half == 0)
                view[k['ANCHOR_IS_B']] = int(half == 1)
                view[k['CAM_ENTRY_A']] = 0
                view[k['CAM_ENTRY_A'] + 1] = 0
                ports.set_view(0, view)
                for origin in range(13):
                    for bank in range(2):
                        for side in range(2):
                            ports.fast[(origin, bank, 3+k['VIEW_WORDS']+side)] = 1200
                            ports.fast[(origin, bank, 3+k['VIEW_WORDS']+2+side)] = 0
                ports.fields[(0, k['CUT_PORT'], 0, 0)] = 20
                ports.fields[(0, k['CUT_PORT'], 1, 0)] = 20
                other = m.W[k['TARGET_BASE'] + k['TARGET_WORDS']:]
                code = m.C[:]
                glob = m.W[:k['TARGET_BASE']]
                m.enter('helper', (0,))
                start = m.steps
                require(m.run(ports, until_yield=False) == 'halt', 'Helper did not finish')
                require(m.C == code, 'Status changed actual running C')
                require(m.W[k['TARGET_BASE']+k['TARGET_WORDS']:] == other,
                        'Status changed another target private state')
                require(all(a == b for j, (a, b) in enumerate(zip(glob, m.W[:k['TARGET_BASE']]))
                            if j >= k['STACK_WORDS'] and j != k['EST_VALID']),
                        'Unexpected global mutation')
                require(all(target == 0 for target, port, side, index in ports.fields),
                        'Other-target effect issued')
                require(not any(port == k['CUT_PORT'] and value > 0
                                for (target, port, side, index), value in ports.fields.items()),
                        'False status bypassed actual unsafe functional field')
                actions.update((e[6], e[8]) for e in ports.events if e[0] == 'command')
                maxsteps = max(maxsteps, m.steps-start)
                cases += 1
    return dict(cases=cases, maximum_retired_instructions=maxsteps, actions=sorted(actions),
                positive_cut_withdrawn=True, other_target_W_preserved=True, C_preserved=True,
                scope='Actual instruction decoder with small address counts and13 origins; no physical path or all-history noninterference proof')


def digest(name):
    text = (HERE/name).read_text(encoding='utf-8-sig').replace('\r\n', '\n')
    return sha256(text.encode('utf-8')).hexdigest()


def main():
    require(not sys.flags.optimize, 'Optimized execution is not a checking mode')
    parser = argparse.ArgumentParser()
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    names = ('EFFECTS.md', 'FAULT-MAP.md', 'Effects.lean', 'effects_model.py',
             'program_model.py', 'program_source.py', 'program_results.json',
             'incidence_model.py', 'INCIDENCE.md', 'HYBRID.md', 'RUNTIME-PORTS.md')
    before = {name:digest(name) for name in names}
    record = HERE/'effects_results.json'
    if args.check:
        expected = json.loads(record.read_text(encoding='utf-8'))
        require(expected['sources'] == before, 'Effects sources changed; review before refresh')
    result = dict(status='conditional effect refinement and bounded code/source review; no source admission',
        sources=before,
        graphs=graph_checks(), envelopes=heterogeneous_envelopes(),
        counterexamples=physical_counterexamples(), weighted_plant=weighted_plant_checks(), shared_switch=shared_switch_check(),
        executed_status_confinement=shared_target_status_probe())
    rendered = json.dumps(result, sort_keys=True, indent=2)+'\n'
    require(before == {name:digest(name) for name in names}, 'Effects inputs changed during checking')
    if args.write:
        record.write_text(rendered, encoding='utf-8')
        print('effects record written')
    else:
        require(record.read_text(encoding='utf-8') == rendered, 'Effects record stale')
        print('effects record matches')


if __name__ == '__main__':
    main()
