"""Phase-10 common-response candidate: actual ISA paths plus exact local bounds.

This is not a hybrid simulation or a proof of positive-family admission.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as Q
import json
import subprocess
import sys
import threshold_program_model as program
import threshold_design as design
import threshold_incidence_model as incidence
import threshold_publication_model as publication

HERE = program.HERE
PREFIX = 'theories-and-designs/byzantine-control/'
SOURCE_BASE = '811b6aab8452e95cf2ba2a47330f8d9247514778'
FIELD_BASE = '70ac3c8678e0de5a01136a11d6e97d321a088b0c'
COUPLING_BASE = 'e9346383a8c20486992fcb71a543ef8f7bbb9d90'
need = program.need


def immutable(commit, relative):
    return subprocess.check_output(['git', 'show', commit + ':' + PREFIX + relative],
                                   cwd=program.REPO).decode('utf-8-sig').replace('\r\n', '\n')


def physical_view(isa, c):
    """Consistent contact/pose branch, not a manufactured reachable CPU state."""
    k = c.constants
    view = isa.populated_view(c, 0, 10)
    view[k['ANCHOR']] = 1
    view[k['BLEND']] = k['BLEND_LIMIT']
    view[k['ANCHOR_IS_A']] = 0
    view[k['ANCHOR_IS_B']] = 1
    for side in (0, 1):
        entries = {'CUT_A': 0, 'CUT_OPEN_A': 0, 'CLAMP_A': k['CLAMP_LIMIT'],
                   'CLAMP_OPEN_A': 0, 'RESET_A': k['RESET_LIMIT'], 'RESET_OPEN_A': 0,
                   'SEAT_A': 12000, 'ACT_A': k['WARM_AT'], 'ACT_ZERO_A': 0,
                   'ACT_POWER_A': 1, 'ISO_DEF_A': 0, 'ISO_SEATED_A': 1,
                   'SHUNT_DEF_A': 0 if side == 0 else 1000,
                   'SHUNT_SEATED_A': int(side == 0), 'SHUNT_OPEN_A': int(side == 1),
                   'POWER_OFF_A': int(side == 0), 'BLEND_AT_A': int(side == 1),
                   'ENERGY_A': 0 if side == 0 else k['RESERVE_CAP']}
        for name, value in entries.items():
            view[k[name] + side] = value
    return view


def maintenance_receipts(isa, c, b, Ports, population, view, load):
    receiver = 0
    ordinal = 39
    k = c.constants
    target, pairs = incidence.maintenance_group(population, receiver, ordinal)
    receipts = []
    steps = calls = samples = offers = max_call = 0
    cursors = []
    for provider, local in pairs:
        ports = Ports(c)
        machine = program.initialized(isa, c)
        for relative, value in enumerate(view):
            ports.fast[('head', 3 + local*k['FAST_TARGET_KEYS'] + relative)] = value
        for side in (0, 1):
            for member in range(11):
                ports.functional[(local, side, member, 0)] = k['SENSE_BIAS'] + (load if side == 0 else 2031)
                ports.functional[(local, side, member, 1)] = k['SENSE_BIAS'] + 1000
        start = local*k['RAW_TARGET_HEADS']
        cursor = (start//k['FAST_BATCH'])*k['FAST_BATCH']
        machine.W[k['FAST_CURSOR']] = cursor
        while machine.W[k['FAST_CURSOR']] < start + k['RAW_TARGET_HEADS']:
            before = machine.steps
            # The interpreter measures its budget relative to this call's start.
            program.call(isa, c, ports, 'publish_fast', (),
                         b['instruction_upper_bounds']['publish_fast'] + 10, machine)
            elapsed = machine.steps - before
            need(elapsed <= b['instruction_upper_bounds']['publish_fast'], 'Producer call exceeded its own bound')
            max_call = max(max_call, elapsed)
            steps += elapsed
            calls += 1
        receipts.extend(publication.deliveries(c, population, provider, 1, ports, receiver, 1))
        samples += ports.samples
        offers += ports.offers
        cursors.append([provider, local, cursor, machine.W[k['FAST_CURSOR']]])
    key = 3 + ordinal*k['FAST_TARGET_KEYS']
    relevant = [r for r in receipts if key <= r.destination_key < key + k['FAST_TARGET_KEYS']]
    need(len(relevant) == 15*k['FAST_TARGET_KEYS'], 'Incomplete actual target publication')
    need(all(r.provider_bank == 1 for r in receipts), 'Unpowered sibling supplied evidence')
    return receipts, dict(actual_target=target, receiver=receiver, receiver_bank=1, receiver_target_ordinal=ordinal,
                          providers=[j for j, _ in pairs], cursors=cursors,
                          producer_calls=calls, producer_instructions=steps, maximum_call_instructions=max_call,
                          raw_samples=samples, accepted_offers=offers,
                          all_mapped_receipts=len(receipts), target_receipts=len(relevant),
                          provider_banks=[1], retiring_load=load,
                          scope='Actual cyclic-block suffixes, not boot/full chronological producer histories')


def helper_check(isa, c, b, Ports, receipts, load, bad_count=0, bad_value=0):
    k = c.constants
    ordinal = 39
    ports = Ports(c)
    publication.install(ports, receipts)
    key = 3 + ordinal*k['FAST_TARGET_KEYS'] + k['VIEW_WORDS']
    need(all(ports.fast[(slot, 1, key)] == load and
             ports.fast[(slot, 1, key+1)] == 2031 and
             ports.fast[(slot, 1, key+2)] == 0 and
             ports.fast[(slot, 1, key+3)] == 0 for slot in range(15)), 'Actual functional fold differs')
    need(all((slot, 0, key) not in ports.fast for slot in range(15)), 'Sibling bank receipt present')
    for slot in range(bad_count):
        ports.fast[(slot, 0, key)] = bad_value
        ports.fast[(slot, 1, key)] = bad_value
    machine = program.initialized(isa, c)
    base = k['TARGET_BASE'] + ordinal*k['TARGET_WORDS']
    # Representatives of the normal already-settled branch. Their historical
    # formation is a separately named source premise, not inferred from W edits.
    for name, value in (('STAGE_ID', 11), ('WATCH_HALF', 1), ('LAST_PHASE', 10),
                        ('HIGH', 250162000), ('TIMER', 2300000000), ('RANK_VALID', 1)):
        machine.W[base+k[name]] = value
    program.call(isa, c, ports, 'helper', (ordinal,), b['instruction_upper_bounds']['helper']+100, machine)
    command = next(e for e in reversed(ports.events) if e[0] == 'command')
    permits = load <= 500 if bad_count <= 7 else bad_value <= 500
    expected_action = k['CUT_PORT'] if permits else 0
    need(command[6] == expected_action and command[4] == k['FORCE'], 'Unexpected actual helper response')
    need(command[8] == (k['FORCE'] if permits else 0), 'Unexpected positive CUT amplitude')
    need(machine.W[base+k['ABORT']] == 0, 'Normal fixture entered abort')
    return dict(load=load, bad_slots=bad_count, replacement=bad_value,
                instructions=machine.steps, command=list(command[1:]), abort=0,
                fixture_scope='Executed normal-branch representative; not a reachable-W certificate')


def world_check(isa, c, b, Ports, population, rows=(500,1000), expected=(60,60)):
    receipts = []
    steps = offers = 0
    providers = sorted(set(incidence.plant_group(population, 0, 0)) |
                       set(incidence.plant_group(population, 0, 1)))
    for provider in providers:
        ports = Ports(c)
        value = rows[incidence.head_type(provider)]
        # Both direct probes belong to the same installed rank-one type.
        ports.fast[('head', 0)] = value
        ports.fast[('head', 1)] = value
        machine = program.call(isa, c, ports, 'publish_plant', (),
                               b['instruction_upper_bounds']['publish_plant']+10)
        receipts.extend(publication.deliveries(c, population, provider, 1, ports, 0, 1))
        steps += machine.steps
        offers += ports.offers
    result, consumer_steps = publication.consume_world(isa, c, b, Ports, receipts, rows[0], rows[1], 0)
    need(result == expected and len(receipts) == 30, 'Actual single-bank WORLD path differs')
    return dict(actual_producers=len(providers), provider_banks=[1],
                producer_instructions=steps, accepted_offers=offers, receipts=len(receipts),
                receiver_prefix_instructions=consumer_steps, raw_rows=list(rows), world=list(result),
                scope='Production frame through first WORLD; no post-output frame pacing simulated')


def arithmetic(c, b, field, geometry):
    k = c.constants
    tau = Q(2**29)
    rho = Q(field['point']['mechanics']['total_reaction'])
    need(rho == Q(81,250), 'Changed complete reaction bound')
    fmax = Q(b['padded_frame_upper'], 2**26) + Q(7,64)
    fmin = Q(100,101)
    visit = 11*fmax
    compare = Q(b['instruction_upper_bounds']['helper']+64, 2**26) + Q(1,64)
    horizon = Q(field['point']['mechanics']['actual_horizon'])
    need(Q(field['point']['mechanics']['clearance_W_over_tau']) < 16, 'Imported cleared-side comparison fails')
    need(Q(field['point']['mechanics']['load_upper']) < 1 and Q(field['point']['mechanics']['gap_lower']) > Q(4,5), 'Imported functional continuation fails')
    driver_to_warm = (Q(k['WARM_AT'])-Q(k['POWER_AT'])-design.VECTOR_DRIVER_OFFSET)/Q(11,10)
    need(driver_to_warm > 10000, 'Actual driver-to-warm interval omits tracker settling')
    # B remains connected: its real on-mode spring load is also represented.
    keeper_v = Q(16644*64,4097)
    keeper_i = Q(16644,4097)
    keeper_error = (Q(field['point']['mechanics']['W_over_tau'])+keeper_v+keeper_i)/11**10 + rho/63
    keeper_settle = 100*tau/63
    keeper_load_interval = [(keeper_v-keeper_error)/128,(keeper_v+keeper_error)/128]
    need(keeper_settle < driver_to_warm, 'Keeper mechanical data lack real on-time')
    need(Q(4061,2000) < keeper_load_interval[0] <= keeper_load_interval[1] < Q(4063,2000), 'Serving B does not quantize to2031')
    need(fmax == Q(1163265,1048576), 'Pacing/image interface changed')
    need(compare < Q(1,8), 'Chosen propagation delay cannot hide new data during helper')
    imax, vmax = Q(21,5), Q(261)
    imin = -rho/64
    need(64*imax > vmax+rho and 16644-64*vmax-imin < 0, 'On-box faces fail')
    on_speed = 16644-imax-64*255
    on_time = (255-172)*Q(3,2)*tau/on_speed
    need(on_speed > 0 and on_time < Q(k['WARM_AT'],1)/Q(11,10), 'On antecedent lacks actual travel time')
    settle = Q(2748532811,524288)
    need(Q(geometry['arithmetic']['ordinary_settle']) == settle, 'Geometry no longer supplies repaired settling')
    derivative = Q(1,100) + imax + 64*vmax
    shunt_drop = derivative*2*(settle+40000)/(Q(3,2)*tau)
    need(shunt_drop < 2, 'Isolation/shunt travel may erase chosen high-load antecedent')
    brake_upper = (261-88)*Q(3,2)*tau/(64*88-(Q(1,100)-imin))
    brake_lower = (253-88)*Q(3,2)*tau/derivative
    need(brake_lower > 1000, 'No full real sample window before crossing')
    tube = derivative*visit/tau
    spread = (2*rho/32)/(Q(3,2)*128)
    drift = derivative/(Q(3,2)*tau*128)
    bias = Q(1,5000)
    sample_low = Q(11,16)-spread-tube/192+bias
    sample_high = Q(11,16)+spread+1000*drift+bias
    need(Q(1375,2000) < sample_low <= sample_high < Q(1377,2000), 'Some quantized head is not 688')
    need(bias+Q(1,2000) < Q(1,100), 'Head offset plus quantization exceeds raw error')
    jump_work = Q(132)**2*tau/6
    stock = Q(field['point']['mechanics']['parameter_stock'])
    need(jump_work == 2904*tau and stock > jump_work, 'Funded exact request unavailable at full J')
    refund = Q(258)**2*tau/6
    low_effect_upper = Q(11,16)+spread+derivative*horizon/(Q(3,2)*tau*128)
    high_effect_lower = (132-tube-derivative*horizon/tau)/128
    need(low_effect_upper < 1 < high_effect_lower, 'Finite effect-horizon admissibility no longer differs')
    fresh = 2*fmax+1+2+226*fmax+2+visit+compare+3
    clear = Q(15,32)*tau
    phase10 = Q(geometry['arithmetic']['phase_bounds']['10_old_cut_drain'])
    earliest = Q(geometry['arithmetic']['watchdog']['earliest'])
    need(clear+fresh < phase10 < earliest, 'Finite continuation escapes source phase/watch budget')
    # General induction is not imported: this is a homogeneous finite service witness.
    tracker = Q(2,11**10)
    service_window = settle+k['BLEND_LIMIT']+phase10
    world_drift = Q(1,10**7)*tracker*service_window
    need(world_drift < Q(2,10**9), 'Homogeneous service witness leaves its row plateau')
    need(2*world_drift < Q(1,2000), 'Sum row needs another integer word')
    need(Q(3,5)-tracker > Q(1,10), 'Actual tracker service fails')
    resources = field['point']['resources']
    reserve = Q(resources['upstream_capacity'])-Q(resources['upstream_burst'])-2*Q(resources['upstream_rate'])
    need(reserve == Q('3608521197514218926289947/400000') > 1, 'Reset-inclusive reserve differs')
    need(reserve == Q(resources['usable_reserve_lower']), 'Imported stock algebra disagrees')
    need(Q(resources['post_on_margin']) > 0, 'Keeper continuation lacks carrier margin')
    return dict(tau=tau, reaction=rho, frame_max=fmax, frame_min=fmin, visit=visit,
                helper_allowance=compare, selected_propagation=Q(1,8), effect_horizon=horizon,
                on_time_upper=on_time, shunt_drop_upper=shunt_drop, brake_time_upper=brake_upper,
                brake_time_lower=brake_lower, q_crossing_tube=tube, all_head_load_spread=spread,
                biased_sample_interval=[sample_low,sample_high], raw_bias=bias,
                low_instant=Q(11,16), high_instant=Q(33,32),
                low_effect_upper=low_effect_upper, high_effect_lower=high_effect_lower,
                jump_work=jump_work, initial_compliance_refund_per_module=refund,
                actual_J_when_no_positive_requests=stock, clearance=clear,
                keeper_mechanical_settling=keeper_settle, keeper_load_interval=keeper_load_interval,
                fresh_data_and_action_after_clearance=fresh, phase10_upper=phase10,
                earliest_watchdog=earliest, repaired_settling=settle,
                tracker_error_after10000=tracker, minimum_driver_to_warm=driver_to_warm, service_window=service_window,
                world_drift_upper=world_drift, service_lower=Q(3,5)-tracker,
                updated_reserve_lower=reserve, keeper_post_on_margin=Q(resources['post_on_margin']),
                source_admission=False)


def normalize(value):
    if isinstance(value,Q):
        return str(value)
    if isinstance(value,dict):
        return {k:normalize(v) for k,v in value.items()}
    if isinstance(value,(list,tuple)):
        return [normalize(v) for v in value]
    return value


def generate():
    isa = program.load_isa()
    c = program.compile_program(isa,design.design(isa))
    b = program.bounds(isa,c)
    Ports = program.ports_class(isa)
    population = 12*(6+2**98)+2
    field_text = immutable(FIELD_BASE,'portability/threshold_field_source_results.json')
    field = json.loads(field_text)
    for name, expected in field['sources_sha256_lf'].items():
        need(program.hash_text(immutable(FIELD_BASE,'portability/'+name)) == expected, 'Imported field source hash differs: '+name)
    geometry_text = immutable(SOURCE_BASE,'portability/threshold_geometry_results.json')
    geometry = json.loads(geometry_text)
    need(program.hash_text(json.dumps(c.image)) == geometry['changed_image_sha256'], 'Changed executable differs from geometry')
    need(b == geometry['bounds'], 'Compiled work bounds differ from geometry')
    print('executing full-cohort fifteen-provider folds and phase-10 helper',flush=True)
    view = physical_view(isa,c)
    receipts, producer = maintenance_receipts(isa,c,b,Ports,population,view,688)
    low_receipts, low_producer = maintenance_receipts(isa,c,b,Ports,population,view,135)
    helpers = [helper_check(isa,c,b,Ports,receipts,688),
               helper_check(isa,c,b,Ports,receipts,688,7,0),
               helper_check(isa,c,b,Ports,low_receipts,135),
               helper_check(isa,c,b,Ports,low_receipts,135,7,3000)]
    world = world_check(isa,c,b,Ports,population)
    exact = arithmetic(c,b,field,geometry)
    drift = exact['world_drift_upper']
    nearest = lambda x: (1000*x+Q(1,2)).__floor__()
    plateau = [nearest(Q(1,2)-drift),nearest(Q(1,2)+drift),
               nearest(1-2*drift),nearest(1+2*drift)]
    need(plateau == [500,500,1000,1000], 'Selected nearest quantizer does not preserve plateau')
    floor_point = Q(1,2)-Q(1,10**9)
    floor_rows = ((1000*floor_point).__floor__(),(2000*floor_point).__floor__())
    need(floor_rows == (499,999), 'Floor-quantizer countercase changed')
    floor_world = world_check(isa,c,b,Ports,population,floor_rows,(59,60))
    source_files = ('common_response.py','COMMON-RESPONSE.md','threshold_program_source.py',
                    'threshold_program_model.py','threshold_design.py','threshold_incidence_model.py',
                    'threshold_publication_model.py','constructors.py')
    immutable_inputs = {
        SOURCE_BASE+':portability/THRESHOLD-GEOMETRY.md':immutable(SOURCE_BASE,'portability/THRESHOLD-GEOMETRY.md'),
        SOURCE_BASE+':portability/threshold_geometry_results.json':geometry_text,
        FIELD_BASE+':portability/threshold_field_source_results.json':field_text,
        FIELD_BASE+':portability/THRESHOLD-FIELD-SOURCE.md':immutable(FIELD_BASE,'portability/THRESHOLD-FIELD-SOURCE.md'),
        FIELD_BASE+':portability/threshold_field_source.py':immutable(FIELD_BASE,'portability/threshold_field_source.py'),
        COUPLING_BASE+':portability/REGIONAL-COUPLING.md':immutable(COUPLING_BASE,'portability/REGIONAL-COUPLING.md')}
    for name in ('PORT-SOURCE.md','INITIAL-RETURN.md','COUPLED-PORTS.md'):
        immutable_inputs[SOURCE_BASE+':local-control/'+name] = immutable(SOURCE_BASE,'local-control/'+name)
    return normalize(dict(scope='Executed source-shaped local mechanism and derived conditional finite-history construction',
        source_base=SOURCE_BASE, field_source_base=FIELD_BASE,
        coupling_base=subprocess.check_output(['git','rev-parse',COUPLING_BASE],cwd=program.REPO).decode().strip(),
        python_version=sys.version, population=str(population),
        image_cells=len(c.image), actual_image_sha256=program.hash_text(json.dumps(c.image)),
        frozen_isa_sha256=isa.source_hash,
        sources_sha256_lf={name:program.digest(HERE/name) for name in source_files},
        immutable_inputs_sha256_lf={name:program.hash_text(text) for name,text in immutable_inputs.items()},
        changed_design=design.physical_parameters(c), physical_view=view,
        normal_action_premises=geometry['arithmetic']['normal_action_premises'],
        producer_688=producer, producer_135=low_producer, helpers=helpers, world=world, exact=exact,
        selected_world_quantizer=dict(rule='floor(1000*z+1/2)',error_at_most=Q(1,2000),
            plateau_endpoint_outputs=plateau,selected_witness_not_all_error_bounded_heads=True),
        floor_countercase=dict(actual_x=floor_point,actual_y=floor_point,raw_error_less_than=Q(1,1000),
            executed=floor_world,scope='admitted head-error/code countercase to universal constant-command plateau; not a whole-source losing history'),
        retained_boundary_cases=['phase0 does not supply this fresh loaded-side history',
            'CUT_OPEN is disconnected-endpoint evidence, not connected-bank evidence',
            'available J is required; capacity does not fund an empty store',
            'first post-clear offer can contain old fold members',
            '135 is a permission-path check, not a claimed snapshot at the clearance deadline'],
        unclosed=['actual common-history phase10 entry and body/code/field formation',
                  'intermediate shunt feed profile and coherent eleven-module physical map',
                  'timed native publication/receipt/command port realization',
                  'complete parent-input/full-ISA cost and legacy inventory domination',
                  'actual normal-stop/abort/private-state formation and pulse/retirement supplier',
                  'source-class admission and whole-family recurrent/positive-density closure'],
        no_full_hybrid_simulation=True, independent_local_review=True,
        rp3_completion=False, source_admission=False, program_completion=False))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    group=parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--write',action='store_true')
    group.add_argument('--check',action='store_true')
    args=parser.parse_args()
    result=generate()
    path=HERE/'common_response_results.json'
    if args.write:
        path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n',encoding='utf-8',newline='\n')
    else:
        need(json.loads(path.read_text(encoding='utf-8'))==result,'Common-response record differs')
    print('PASS source-shaped common-response candidate; full source/RP3 admission remains open')


if __name__=='__main__':
    main()
