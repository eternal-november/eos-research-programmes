"""Finite energy-backed signed-force transducer: source equations and adversarial checks.

The ordinary port state is two bounded currents, never a truth/permission bit.
Analytic event segments retain exact zero events; traces are test evidence.
"""
from __future__ import annotations
import argparse
import ast
from dataclasses import dataclass, field
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations
import json
import math
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
R = F(100)
RMAX = F(101)
UMIN_NOMINAL = F(299)
KAPPA = F(11, 15)
VMAX = F(11, 10)
XMAX = F(3)
UMAX = F(300)
BRAKES = 7
FAULTS = 6
BRAKE_NOMINAL = F(2)
BRAKE_FAILED_MAX = F(4)
TOL = 2e-8


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def close(a, b, message):
    require(abs(a-b) <= TOL*(1+abs(a)+abs(b)), message)


def digest(path):
    return sha256(path.read_text(encoding='utf-8-sig').replace('\r\n', '\n').encode()).hexdigest()


@dataclass
class Channel:
    """A fixed endpoint and direction; x is current, E=x*x, L=2."""
    sign: int
    x: float = 0.0
    brakes: list[float] = field(default_factory=lambda: [2.0]*BRAKES)
    failed: set[int] = field(default_factory=set)
    resistance: float = 100.0
    initial: float = field(init=False)
    supplied: float = 0.0
    resistor_heat: float = 0.0
    brake_heat: float = 0.0
    mechanical: float = 0.0
    elapsed: float = 0.0

    def __post_init__(self):
        require(self.sign in (-1, 1), 'Direction is not a fixed physical orientation')
        require(0 <= self.x <= float(XMAX), 'Initial current outside capacity')
        require(float(R) <= self.resistance <= float(RMAX), 'Resistance outside retained passive family')
        self.initial = self.x*self.x
        self.validate()

    def validate(self):
        require(len(self.brakes) == BRAKES and len(self.failed) <= FAULTS, 'Invalid finite brake inventory')
        require(all(0 <= j < BRAKES for j in self.failed), 'Fault identity outside physical regions')
        require(all(0 <= k <= float(BRAKE_FAILED_MAX) and (j in self.failed or k == 2) for j,k in enumerate(self.brakes)), 'Uncharged or nonpassive brake change')
        require(float(R) <= self.resistance <= float(RMAX), 'Series resistance bypass is outside this family')
        require(0 <= self.x <= float(XMAX), 'Physical current escaped the proved state set')

    def damage(self, branch, coefficient):
        require(0 <= branch < BRAKES and 0 <= coefficient <= float(BRAKE_FAILED_MAX), 'Invalid passive fault')
        require(len(self.failed | {branch}) <= FAULTS, 'Outside admitted retained branch-failure count')
        self.failed.add(branch)
        self.brakes[branch] = float(coefficient)
        self.validate()
        # The fault changes a passive constitutive element, not current/energy.

    @property
    def force(self):
        return self.sign*float(KAPPA)*self.x

    @property
    def heat(self):
        return self.resistor_heat+self.brake_heat

    def advance(self, duration, voltage, velocity):
        """Integrate one constant-input segment, splitting actual endpoint hits."""
        self.validate()
        dt = float(duration)
        u, v = float(voltage), float(velocity)
        require(dt >= 0 and 0 <= u <= float(UMAX) and abs(v) <= float(VMAX), 'Input outside raw envelope')
        x0 = self.x
        g = sum(self.brakes)
        b = g+self.sign*float(KAPPA)*v
        resistance = self.resistance
        rate = resistance/2
        equilibrium = (u-b)/resistance
        require(equilibrium < float(XMAX), 'Passive inward cap was lost; no projection can hide it')
        free = dt
        boundary = None
        if x0 == 0 and equilibrium <= 0:
            free, boundary = 0.0, 0.0
        elif equilibrium < 0:
            hit = math.log((x0-equilibrium)/(-equilibrium))/rate
            if hit <= dt:
                free, boundary = max(0.0, hit), 0.0
        if free:
            decay = math.exp(-rate*free)
            a, offset = equilibrium, x0-equilibrium
            ix = a*free+offset*(-math.expm1(-rate*free))/rate
            ix2 = a*a*free+2*a*offset*(-math.expm1(-rate*free))/rate+offset*offset*(-math.expm1(-2*rate*free))/(2*rate)
            x1 = a+offset*decay
        else:
            ix = ix2 = 0.0
            x1 = x0
        if boundary is not None:
            x1 = boundary
            rest = dt-free
            ix += boundary*rest
            ix2 += boundary*boundary*rest
        require(-TOL <= x1 <= float(XMAX)+TOL, 'State escaped its proved passive interval')
        x1 = max(0.0, x1)
        supplied, rh, bh = u*ix, resistance*ix2, g*ix
        work = self.sign*float(KAPPA)*v*ix
        close(x1*x1-x0*x0, supplied-rh-bh-work, 'Segment violates power balance')
        require(min(rh, bh) >= -TOL, 'A passive element generated energy')
        require(supplied <= 900*dt+TOL and rh+bh <= 987*dt+TOL, 'Continuous source/heat envelope violated')
        require(abs(work) <= 2.42*dt+TOL, 'Mechanical input/output was unbounded')
        self.x = x1
        self.supplied += supplied
        self.resistor_heat += rh
        self.brake_heat += bh
        self.mechanical += work
        self.elapsed += dt
        close(self.initial+self.supplied, self.x*self.x+self.heat+self.mechanical, 'Cumulative energy was lost or double counted')
        return dict(integral_current=ix, integral_current_squared=ix2, supplied=supplied, heat=rh+bh, mechanical=work, zero=(self.x == 0))


@dataclass
class Pair:
    positive: Channel = field(default_factory=lambda: Channel(1))
    negative: Channel = field(default_factory=lambda: Channel(-1))

    @property
    def force(self):
        return self.positive.force+self.negative.force

    def advance(self, duration, drive, velocity):
        left = self.positive.advance(duration, drive[0], velocity)
        right = self.negative.advance(duration, drive[1], velocity)
        require(abs(self.force) <= float(KAPPA*XMAX)+TOL, 'Opposed stores exceeded net coordinate cap')
        require(abs(left['mechanical']+right['mechanical']) <= 2.42*float(duration)+TOL, 'Shared-coordinate work bound violated')
        return left, right

    def summary(self):
        channels = (self.positive, self.negative)
        return dict(force=round(self.force, 12), energy=round(sum(c.x*c.x for c in channels), 12), supplied=round(sum(c.supplied for c in channels), 12), heat=round(sum(c.heat for c in channels), 12), mechanical=round(sum(c.mechanical for c in channels), 12))


def decode_amplitude(word, shift):
    return ((word >> shift) & 63)-32


def drive_for(amplitude):
    voltage = float(UMAX)*min(abs(amplitude)/20, 1)
    return (voltage, 0.0) if amplitude > 0 else (0.0, voltage) if amplitude < 0 else (0.0, 0.0)


def parameter_checks():
    gmin = (BRAKES-FAULTS)*BRAKE_NOMINAL
    gmax = BRAKES*BRAKE_NOMINAL+FAULTS*(BRAKE_FAILED_MAX-BRAKE_NOMINAL)
    delta = gmin-KAPPA*VMAX
    require(delta > 0, 'Backdrive can sustain a withdrawn field')
    zero = 2*XMAX/delta
    require(zero == F(900, 179) and zero < 6, 'Uniform exact-zero tail changed')
    work_current = F(2)/KAPPA
    nominal_g = BRAKES*BRAKE_NOMINAL
    require(UMAX-R*XMAX-gmin+KAPPA*VMAX < 0, 'No source-real inward current bound')
    equilibrium = (UMIN_NOMINAL-nominal_g-KAPPA*VMAX)/RMAX
    require(XMAX > equilibrium > work_current, 'Nominal constant command cannot sustain useful force')
    rise_rational = (2/RMAX)*work_current/(equilibrium-work_current)
    require(rise_rational < F(19,25), 'Exact log upper bound does not certify nominal deadline')
    zero_rational = F(4,25)
    require(1+R*XMAX/delta < 2**8, 'Eight dyadic log intervals no longer certify zero deadline')
    require(F(2)+F(1,64)+max(rise_rational,zero_rational) < 3, 'Rational delivery/force certificate failed')
    rise = float(2/RMAX)*math.log(float(equilibrium/(equilibrium-work_current)))
    nominal_opposite_zero = float(2/R)*math.log(float(1+R*XMAX/(nominal_g-KAPPA*VMAX)))
    require(nominal_opposite_zero < rise < .76, 'Signed nominal reversal exceeds allocated rise')
    require(2+1/64+rise < 3, 'Command transport plus actual force rise exceeds3')
    peak_pair_heat = 2*(RMAX*XMAX*XMAX+gmax*XMAX)
    require(peak_pair_heat == 1974, 'Heat bound changed')
    tight_zero = float(2/R)*math.log(float(1+R*XMAX/delta))
    return dict(capacity_per_store=9, capacity_per_signed_pair=18, max_gross_power_per_store=900, max_gross_power_both_driven=1800, max_nominal_sign_exclusive_power=900, uniform_velocity=str(VMAX), fixed_force_gain=str(KAPPA), current_cap_derived=3, source_voltage_cap=300, nominal_full_voltage_range=[299,300], series_resistance_range=[100,101], braking_cells=BRAKES, retained_brake_faults=FAULTS, failed_cell_drop_range=[0, 4], minimum_braking_drop=str(gmin), maximum_braking_drop=str(gmax), net_decay_drop=str(delta), exact_zero_tail_coarse=str(zero), exact_zero_tail_tight=round(tight_zero,12), exact_zero_tail_rational=str(zero_rational), nominal_rise_rational=str(rise_rational), delivery_force_rational=str(F(2)+F(1,64)+max(rise_rational,zero_rational)), no_upper_state_projection=True, nominal_rise=round(rise, 12), nominal_opposite_zero=round(nominal_opposite_zero, 12), command_plus_nominal_rise=round(2+1/64+rise, 12), failed_reversal_with_weak_brakes=round(2+1/64+max(rise,tight_zero),12), coarse_failed_reversal_with_weak_brakes=round(2+1/64+float(zero), 12), peak_heat_both_stores=str(peak_pair_heat), heat_interval_burst=18, heat_interval_rate=str(2*UMAX*XMAX+KAPPA*XMAX*VMAX), nominal_heat_interval_rate=str(UMAX*XMAX+KAPPA*XMAX*VMAX), independent_velocity_heat_interval_rate=str(2*UMAX*XMAX+2*KAPPA*XMAX*VMAX), output_net_cap=str(KAPPA*XMAX), opposed_unsigned_force_cap=str(2*KAPPA*XMAX))


def endpoint_checks():
    cases = 0
    for count in range(FAULTS+1):
        for failed in combinations(range(BRAKES), count):
            for sign in (-1, 1):
                for initial in (0.0, .5, 1.0, 2.0, 3.0):
                    for velocity in (-1.1, 0.0, 1.1):
                        c = Channel(sign, initial)
                        for branch in failed:
                            c.damage(branch, 0)
                        c.advance(F(900, 179), 0, velocity)
                        require(c.x == 0 and c.force == 0, 'Withdrawal only became small, not zero')
                        c.advance(100, 0, -velocity)
                        require(c.x == 0, 'Zero was rearmed by bounded target backdrive')
                        cases += 1
    last = Channel(-1, 3)
    for branch in range(FAULTS):
        last.damage(branch, 0)
    exact = float(2/R)*math.log(float(1+R*XMAX/(2-KAPPA*VMAX)))
    last.advance(exact-1e-6, 0, 1.1)
    require(last.x > 0, 'A tolerance threshold replaced true zero support')
    before = last.x
    last.advance(2e-6, 0, 1.1)
    require(last.x == 0, 'The exact boundary event did not terminate pressure')
    return dict(exact_zero_cases=cases, all_failures_at_worst_passive_bypass=True, zero_absorbing_under_backdrive=True, current_just_before_hit=round(before,12), exact_hit_then_absorbing=True)


def startup_checks():
    cases = 0
    for sign in (-1, 1):
        for initial_plus, initial_minus in ((0, 0), (0, 3), (3, 0), (3, 3), (1, 2)):
            for velocity in (-1.1, 0, 1.1):
                pair = Pair(Channel(1, initial_plus, resistance=101), Channel(-1, initial_minus, resistance=101))
                nominal_drive = (299,0) if sign > 0 else (0,299)
                pair.advance(.76, nominal_drive, velocity)
                require(sign*pair.force >= 2, 'Actual signed force failed nominal deadline')
                pair.advance(100, drive_for(20*sign), -velocity)
                require(sign*pair.force >= 2, 'Nominal held force was not maintained')
                pair.advance(6, (0, 0), velocity)
                require(pair.positive.x == pair.negative.x == 0, 'Neutral did not clear both stores')
                cases += 1
    return dict(signed_start_and_reversal_cases=cases, nominal_force_lower=2, checked_deadline=.76)



def weak_failure_reversal_checks():
    cases=0
    for count in range(FAULTS+1):
        for failed in combinations(range(BRAKES),count):
            for sign in (-1,1):
                for velocity in (-1.1,0,1.1):
                    new=Channel(sign,0,resistance=101)
                    old=Channel(-sign,3,resistance=100)
                    for branch in failed:
                        old.damage(branch,0)
                    pair=Pair(new,old) if sign==1 else Pair(old,new)
                    pair.advance(.12,(299,0) if sign==1 else (0,299),velocity)
                    require(sign*pair.force>=2,'Weak brake failures defeated the derived stable-sign deadline')
                    cases+=1
    return dict(reversal_cases=cases,maximum_retained_fault_regions=6,checked_endpoint_deadline=.12,other_channel_worst_startup=True)


def decoding_checks():
    neutral = 32*64+32*4096+32*(1 << 40)
    require(all(decode_amplitude(neutral, s) == 0 for s in (6, 12, 40)), 'Neutral word is not zero drive')
    require(all(decode_amplitude(0, s) == -32 for s in (6, 12, 40)), 'Raw all-zero-word obstruction lost')
    for raw in range(64):
        drive = drive_for(raw-32)
        require(all(0 <= x <= float(UMAX) for x in drive) and min(drive) == 0, 'Record decoder energized both directions')
    return dict(raw_amplitudes=64, neutral_record=neutral, raw_zero_record_amplitude=-32, nominal_requested_amplitudes=[-20, 0, 20], arbitrary_simultaneous_physical_drive_separately_tested=True)


def traces():
    records = []
    for initial in ((0, 0), (3, 3), (0, 3)):
        pair = Pair(Channel(1, initial[0]), Channel(-1, initial[1]))
        for j in range(90):
            amplitude = (-32, 20, 0, 31, -20, 1, 0, -1, 20)[j % 9]
            velocity = (-1.1, 0, 1.1)[j % 3]
            pair.advance(F(1+(j % 7), 10), drive_for(amplitude), velocity)
        pair.advance(6, (0, 0), 1.1)
        require(pair.positive.x == pair.negative.x == 0, 'Hostile command history survived stable neutral')
        records.append(pair.summary())
    # Actual physical fault can energize both stores; net cap is not a heat cap.
    pair = Pair(Channel(1, 3), Channel(-1, 3))
    pair.advance(20, (300, 300), 0)
    require(pair.force == 0 and pair.positive.x == pair.negative.x and pair.positive.x > 2.7, 'Opposed-pressure witness lost')
    records.append(pair.summary())
    for branch in range(FAULTS//2):
        pair.positive.damage(branch, 0)
        pair.negative.damage(branch, 4)
    for j in range(100):
        pair.positive.damage(0, (0,4)[j % 2])
        pair.negative.damage(0, (4,0)[j % 2])
        pair.advance(F(1, 10), (0, 0), (-1.1, 1.1)[j % 2])
    require(pair.positive.x == pair.negative.x == 0, 'Passive faults prevented uniform zero')
    records.append(pair.summary())
    return dict(adversarial_command_segments=270, simultaneous_drive=True, changed_passive_coefficients=True, post_fault_backdrive_segments=100, repeated_changes_do_not_reset_failure_count_or_energy=True, records=records)


def multiple_fields():
    fields = [Pair(Channel(1, (j % 4)), Channel(-1, ((j+1) % 4))) for j in range(8)]
    for step in range(45):
        velocity = (-1.1, 0, 1.1)[step % 3]
        for j, pair in enumerate(fields):
            pair.advance(F(1, 5), drive_for((20, -20, 0)[(j+step) % 3]), velocity)
        require(abs(sum(pair.force for pair in fields)) <= 8*2.2+TOL, 'Field summation reused a coordinate cap')
    for pair in fields:
        pair.advance(6, (0, 0), 1.1)
        require(pair.force == 0 and pair.positive.x == pair.negative.x == 0, 'Some fixed endpoint retained pressure')
    return dict(independent_signed_fields=8, event_segments=45, maximum_net_force_bound='88/5', cleared_by_stable_neutral=True, endpoint_identity_not_reused=True)


def boundaries():
    # The finite-time law is substantive: removing its final cell restores a tail.
    t = 10
    residual = 3*math.exp(-float(R)*t/2)
    require(residual > 0, 'Pure resistor comparison accidentally became exact zero')
    # A stationary spring can retain nonzero pressure with finite energy and no work.
    spring_energy = F(2)*F(1)**2/2
    spring_force = F(2)*F(1)
    require(spring_energy == 1 and spring_force == 2, 'Trapped-pressure counterexample changed')
    # Six failed cells plus excessive backdrive invalidate the positive decay gap.
    excessive_velocity = F(3)
    require(2-KAPPA*excessive_velocity < 0, 'Velocity boundary no longer defeats zero invariance')
    overloaded = Channel(1, resistance=101)
    for branch in range(FAULTS):
        overloaded.damage(branch, 4)
    overloaded.advance(5, 299, 1.1)
    require(overloaded.force < 2, 'High passive dissipation unexpectedly retained useful force')
    overloaded.advance(6, 0, -1.1)
    require(overloaded.force == 0, 'Loss of progress was confused with loss of withdrawal')
    bypassed_resistor_slope = (300-14)/2
    escaped_current = 3+bypassed_resistor_slope*.001
    require(float(KAPPA)*escaped_current > 2.2, 'Resistor-bypass force-cap obstruction lost')
    return dict(resistor_bypass={'initial_current':3,'after_.001':escaped_current,'force_cap_violated':True}, all_brakes_bypassed={'initial_current':3, 'at_t10':format(residual, '.17g'), 'exact_zero_at_finite_time':False}, extra_isolated_spring={'energy':1, 'pressure':2, 'stationary_mechanical_work':0, 'not_covered_by_brake_count':True}, excessive_backdrive_velocity=str(excessive_velocity), raw_output_relation_or_unlisted_store_failure_reopens_theorem=True, more_dissipation_can_destroy_positive_availability=True, source_input_not_removed_means_no_withdrawal_claim=True, component_indexed_and_issuer_origin_claims_distinct=True)



def endpoint_for(action, side, index, bays):
    if not (0 <= index < bays and side in (0,1)):
        return None
    if action == 2:
        return ('blend',)
    if action == 6:
        return ('activation', side, index)
    if action == 10:
        return ('cam',)
    names = {3:'isolation',4:'shunt',5:'cut',7:'clamp',8:'reset',9:'seat'}
    return (names[action],side) if action in names else None


def coordinate_catalogue(bays):
    return {('cam',),('mode',),('blend',)} | {(name,side) for name in ('isolation','shunt','cut','clamp','reset','seat') for side in (0,1)} | {('activation',side,index) for side in (0,1) for index in range(bays)}


def decode_requests(record, bays, normal_cam_gate=True, rewind_gate=True):
    # A diagnostic finite array represented by a dictionary, not a dynamic store map.
    out = {key:0 for key in coordinate_catalogue(bays)}
    if not 0 <= record < (1 << 46):
        return out
    out[('cam',)] = decode_amplitude(record,6) if normal_cam_gate else 0
    out[('mode',)] = decode_amplitude(record,12)
    action,side,index = (record >> 18)&15,(record >> 5)&1,(record >> 22)&((1 << 18)-1)
    key = endpoint_for(action,side,index,bays)
    if key is not None:
        value = decode_amplitude(record,40)
        if action == 10:
            value = -value if rewind_gate else 0
        out[key] += value
    return out


def address_checks():
    bays=80
    catalogue=coordinate_catalogue(bays)
    require(len(catalogue)==15+2*bays==175,'Physical endpoint catalogue changed')
    addresses=0
    reached={('cam',),('mode',)}
    # Exhaustive raw action/side/18-bit index space, including aliases/rejections.
    for action in range(16):
        for side in range(2):
            for index in range(1 << 18):
                key=endpoint_for(action,side,index,bays)
                if key is not None:
                    require(key in catalogue,'A raw address created a new physical endpoint')
                    reached.add(key)
                require(index < bays or key is None,'Out-of-range index allocated a driver')
                addresses+=1
    require(reached==catalogue,'Catalogue contains an unreachable or omitted endpoint')
    neutral=32*64+32*4096+32*(1 << 40)
    require(all(value==0 for value in decode_requests(neutral,bays).values()),'Neutral did not zero every endpoint drive')
    alias_cases=0
    for cam in range(-32,32):
        for rewind in range(-32,32):
            record=(cam+32)*64+32*4096+10*262144+(rewind+32)*(1 << 40)
            requests=decode_requests(record,bays)
            require(requests[('cam',)]==cam-rewind,'CAM/REWIND did not share one signed request')
            require(sum(bool(v) for v in requests.values())<=1,'Alias produced independent charged stores')
            require(max(drive_for(requests[('cam',)]))<=300,'Alias sum defeated physical source voltage bound')
            alias_cases+=1
    # Actual record replacement zeros old endpoint INPUTS, not old energy.
    cut=neutral+5*262144+20*(1 << 40)
    request=decode_requests(cut,bays)
    old=Pair()
    old.advance(1,drive_for(request[('cut',0)]),0)
    request=decode_requests(neutral,bays)
    require(request[('cut',0)]==0 and old.force>0,'Record replacement silently erased physical current')
    old.advance(6,drive_for(request[('cut',0)]),1.1)
    require(old.force==0,'Actual neutral did not drain fixed old endpoint')
    pairs=2*40*len(catalogue)
    return dict(raw_addresses=addresses,alias_value_pairs=alias_cases,actual_coordinates_per_bank_target=len(catalogue),host_signed_pairs=pairs,host_store_capacity=18*pairs,host_gross_all_driver_power=1800*pairs,host_peak_heat=1974*pairs,bankpair_record_fresh_coordinate_upper=3,bankpair_sign_exclusive_source_power_upper=2700,record_replacement_preserves_current_until_drain=True,all_cartridge_mailboxes_share_bank_array=True,mechanical_gate_and_fault_routing_not_proved=True)



def abi_checks():
    import program_model as program
    k=program.Design().constants()
    expected={'MODE_PORT':0,'CAM_PORT':1,'BLEND_PORT':2,'ISO_PORT':3,'SHUNT_PORT':4,'CUT_PORT':5,'ACT_PORT':6,'CLAMP_PORT':7,'RESET_PORT':8,'INSERT_PORT':9,'REWIND_PORT':10}
    require(all(k[name]==number for name,number in expected.items()),'Physical port catalogue differs from PROGRAM ABI')
    neutral=32*64+32*4096+32*(1 << 40)
    require(k['FORCE']==20 and k['NEUTRAL_COMMAND']==neutral,'PROGRAM force/neutral convention changed')
    tree=ast.parse((HERE/'program_source.py').read_text(encoding='utf-8-sig'))
    emits=[]
    for node in ast.walk(tree):
        if isinstance(node,ast.Call) and isinstance(node.func,ast.Name) and node.func.id=='emit':
            expression=ast.unparse(node.args[4])
            require(expression in ('0','FORCE','-FORCE'),'PROGRAM introduced an unbound nominal force magnitude')
            emits.append(expression)
    require(emits,'No actual PROGRAM force calls were checked')
    return dict(nominal_emit_sites=len(emits),nominal_amplitude_expressions=sorted(set(emits)),physical_port_numbers=expected,actual_neutral_matches=True,scope='actual stored-source ABI, not full controller/source refinement')


def main():
    require(not sys.flags.optimize, 'Optimized execution removes evidence checks')
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--write', action='store_true')
    group.add_argument('--check', action='store_true')
    args = parser.parse_args()
    inputs = ('TRANSDUCER.md', 'transducer_model.py', 'program_model.py', 'program_source.py')
    before = {name:digest(HERE/name) for name in inputs}
    output = HERE/'transducer_results.json'
    expected = json.loads(output.read_text(encoding='utf-8')) if args.check else None
    if expected:
        require(expected['sources'] == before, 'Bound transducer sources changed')
    result = dict(schema='finite-signed-transducer-v1', sources=before, scope='ideal fixed-storage passive-brake-fault component; physical layout, full damage coverage and source admission separate', parameters=parameter_checks(), program_abi=abi_checks(), endpoints=endpoint_checks(), startup=startup_checks(), weak_failure_reversal=weak_failure_reversal_checks(), decoding=decoding_checks(), addresses=address_checks(), traces=traces(), multiple_fields=multiple_fields(), boundaries=boundaries())
    require(before == {name:digest(HERE/name) for name in inputs}, 'Source changed during checks')
    if args.write:
        output.write_text(json.dumps(result, sort_keys=True, indent=2)+'\n', encoding='utf-8', newline='\n')
    else:
        require(result == expected, 'Reproduced transducer result differs')
    print('PASS transducer:', result['endpoints']['exact_zero_cases'], 'exact-zero cases;', result['startup']['signed_start_and_reversal_cases'], 'signed startup/reversal cases')


if __name__ == '__main__':
    main()
