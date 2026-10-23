"""Exact executable evidence for INFORMATION.md; Python 3 standard library only.

This is a reference mathematical implementation, not a measured hardware timing
claim. --check compares independent geometric specifications and writes nothing.
--write-results writes only information_results.json beside this source.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import combinations, product
import json
import hashlib
from pathlib import Path
from typing import Iterable

Row = tuple[F, F]
Point = tuple[F, F]
Constraint = tuple[F, F, F]  # a*x+b*y <= c


def frac_bits(v: F) -> int:
    return max(abs(v.numerator).bit_length(), v.denominator.bit_length(), 1)


def dot(h: Row, x: Point) -> F:
    return h[0]*x[0]+h[1]*x[1]


def all_subsets(items: Iterable[int], cap: int):
    items = tuple(items)
    for k in range(min(cap, len(items))+1):
        yield from combinations(items, k)


def domain_family(maps: Iterable[tuple[frozenset[int], ...]], cap: int):
    """Union over incidence maps; each row can depend on several domains."""
    out = set()
    for mapping in maps:
        domains = set().union(*mapping)
        for bad in all_subsets(sorted(domains), cap):
            bad = frozenset(bad)
            out.add(frozenset(i for i, deps in enumerate(mapping) if deps & bad))
    return tuple(sorted(out, key=lambda s: (len(s), tuple(sorted(s)))))


def maximal_sets(family):
    """Dropping a dominated explanation preserves the union of candidate sets."""
    return tuple(s for s in family if not any(s < t for t in family))


def constraints(rows, reports, beta, bad, box=(F(-1), F(1), F(-1), F(1))):
    xl, xu, yl, yu = box
    out = [(F(1), F(0), xu), (F(-1), F(0), -xl),
           (F(0), F(1), yu), (F(0), F(-1), -yl)]
    for i, h in enumerate(rows):
        if i in bad:
            continue
        if reports[i] is None:
            return None
        r, b = reports[i], beta[i]
        out.extend([(h[0], h[1], r+b), (-h[0], -h[1], -r+b)])
    return out


@dataclass
class Meter:
    ops: int = 0
    max_bits: int = 1

    def use(self, *values):
        self.max_bits = max(self.max_bits, *(max(1, abs(v).bit_length()) for v in values))

    def add(self, a, b):
        self.ops += 1
        out = a+b
        self.use(a, b, out)
        return out

    def sub(self, a, b):
        self.ops += 1
        out = a-b
        self.use(a, b, out)
        return out

    def mul(self, a, b):
        self.ops += 1
        out = a*b
        self.use(a, b, out)
        return out

    def le(self, a, b):
        self.ops += 1
        self.use(a, b)
        return a <= b

    def eq(self, a, b):
        self.ops += 1
        self.use(a, b)
        return a == b

    def neg(self, a):
        self.ops += 1
        self.use(a)
        return -a


def integer_row(row, meter):
    """Clear three denominators by products, without unaccounted gcd calls."""
    q = [v.denominator for v in row]
    return tuple(meter.mul(v.numerator, meter.mul(q[(i+1)%3], q[(i+2)%3]))
                 for i, v in enumerate(row))


def det(a, b, c, d, meter):
    return meter.sub(meter.mul(a, d), meter.mul(b, c))


def vertices_exact(cs, meter=None):
    """Raw homogeneous (x numerator,y numerator,positive denominator) vertices."""
    meter = meter or Meter()
    rs = [integer_row(c, meter) for c in cs]
    out = []
    for (a, b, c), (d, e, f) in combinations(rs, 2):
        den = det(a, b, d, e, meter)
        if meter.eq(den, 0):
            continue
        xn = det(c, b, f, e, meter)
        yn = det(a, c, d, f, meter)
        if meter.le(den, 0):
            den, xn, yn = meter.neg(den), meter.neg(xn), meter.neg(yn)
        valid = True
        for aa, bb, cc in rs:
            lhs = meter.add(meter.mul(aa, xn), meter.mul(bb, yn))
            rhs = meter.mul(cc, den)
            if not meter.le(lhs, rhs):
                valid = False
                break
        if valid:
            out.append((xn, yn, den))
    return out


def raw_extrema(vertices, meter):
    """No gcd; consumers may retain unreduced rational extrema."""
    if not vertices:
        return None
    x, y, d = vertices[0]
    ext = [(x, d), (x, d), (y, d), (y, d)]
    for x, y, d in vertices[1:]:
        for k, num in enumerate((x, x, y, y)):
            old, od = ext[k]
            lhs, rhs = meter.mul(num, od), meter.mul(old, d)
            replace = meter.le(lhs, rhs) if k % 2 == 0 else meter.le(rhs, lhs)
            if replace:
                ext[k] = (num, d)
    return tuple(ext)


def decode(rows, reports, beta, family, box=(F(-1), F(1), F(-1), F(1))):
    meter = Meter()
    vertices = []
    coeff_bits = 1
    max_r = 4
    for bad in family:
        cs = constraints(rows, reports, beta, bad, box)
        if cs is None:
            continue
        coeff_bits = max(coeff_bits, *(frac_bits(x) for row in cs for x in row))
        max_r = max(max_r, len(cs))
        vertices.extend(vertices_exact(cs, meter))
    raw = raw_extrema(vertices, meter)
    # Fraction reductions below are specification/output serialization, excluded
    # from the integer-kernel meter; INFORMATION.md separately bounds them.
    ext = None if raw is None else tuple(F(a, b) for a, b in raw)
    midpoint = None if ext is None else ((ext[0]+ext[1])/2, (ext[2]+ext[3])/2)
    count_bound = len(family)*(12*max_r + max_r*(max_r-1)//2*(8*max_r+40))
    return {"bounds": ext, "midpoint": midpoint, "vertices": vertices,
            "integer_ops": meter.ops, "integer_bits": meter.max_bits,
            "coefficient_bits": coeff_bits, "kernel_op_bound": count_bound,
            "kernel_bit_bound": 12*coeff_bits+8}


def clip_polygon(cs, box=(F(-1), F(1), F(-1), F(1))):
    """Independent exact spec: successive edge clipping, no line enumeration."""
    xl, xu, yl, yu = box
    poly = [(xl, yl), (xu, yl), (xu, yu), (xl, yu)]
    for a, b, c in cs:
        if not poly:
            return []
        out = []
        for p, q in zip(poly, poly[1:]+poly[:1]):
            vp, vq = a*p[0]+b*p[1]-c, a*q[0]+b*q[1]-c
            pin, qin = vp <= 0, vq <= 0
            if pin:
                out.append(p)
            if pin != qin:
                t = vp/(vp-vq)
                out.append((p[0]+t*(q[0]-p[0]), p[1]+t*(q[1]-p[1])))
        poly = out
    return poly


def spec_decode(rows, reports, beta, family):
    pts = []
    for bad in family:
        cs = constraints(rows, reports, beta, bad)
        if cs is not None:
            pts.extend(clip_polygon(cs))
    if not pts:
        return None
    return min(p[0] for p in pts), max(p[0] for p in pts), min(p[1] for p in pts), max(p[1] for p in pts)


def candidate_membership(rows, reports, beta, family, x):
    return any(all(i in bad or (reports[i] is not None and abs(dot(h, x)-reports[i]) <= beta[i])
                   for i, h in enumerate(rows)) for bad in family)


def pair_condition(rows, family):
    """Best two-row inverse bound for every pair of domain explanations."""
    worst = F(0)
    for s in family:
        for t in family:
            good = [i for i in range(len(rows)) if i not in s | t]
            kappas = []
            for i, j in combinations(good, 2):
                a, b = rows[i]
                c, d = rows[j]
                determinant = a*d-b*c
                if determinant:
                    kappas.append(max(abs(d)+abs(b), abs(c)+abs(a))/abs(determinant))
            if not kappas:
                return None
            worst = max(worst, min(kappas))
    return worst


def median_group(values, sentinel=F(0)):
    """Fixed length odd group; missing data charged as invalid and replaced."""
    a = [sentinel if v is None else v for v in values]
    comparisons = shifts = 0
    for i in range(1, len(a)):
        v, j = a[i], i
        while j:
            comparisons += 1
            if a[j-1] <= v:
                break
            a[j] = a[j-1]
            shifts += 1
            j -= 1
        a[j] = v
    return a[len(a)//2], comparisons, shifts


def admit(records, epoch, rows, start, close, max_length, max_value):
    """Already origin-labelled bounded ingress records; no claimed sample time.

    Record: (delivery_tick, source_slot, claimed_epoch, encoded_length, value).
    Prefix/header checks are charged for every delivered record. The first valid
    record for a slot wins. Authenticity of origin is an explicit source premise,
    not something this value-level function establishes.
    """
    result = [None]*rows
    work = 0
    for tick, slot, ep, length, value in records:
        work += 6
        if not (start <= tick <= close and 0 <= slot < rows and ep == epoch and 0 <= length <= max_length):
            continue
        if result[slot] is not None:
            continue
        work += max_length
        if isinstance(value, F) and abs(value) <= max_value:
            result[slot] = value
    return result, work


def fixed_packet(slot, epoch, value):
    assert 0 <= slot < 64 and epoch in (0, 1) and -4000 <= value <= 4000
    return slot | (epoch << 6) | ((value & ((1 << 14)-1)) << 7)


def parse_packet(word, origin_slot, epoch, slots):
    # The source presents an already bounded64-bit word and origin-labelled port.
    if not (0 <= word < (1 << 64)) or word >> 21:
        return None
    slot, ep = word & 63, (word >> 6) & 1
    value = (word >> 7) & ((1 << 14)-1)
    if value >= (1 << 13): value -= 1 << 14
    if slot != origin_slot or slot >= slots or ep != epoch or abs(value) > 4000:
        return None
    return value


class QueryQuota:
    def __init__(self, origins):
        self.origins = frozenset(origins)
        self.remaining = {origin: 0 for origin in self.origins}
        self.model_time = 0  # simulator ghost, absent from the local policy state

    def local_tick(self):
        self.remaining = {o: max(0,r-1) for o,r in self.remaining.items()}

    def accept(self, tick, physical_origin, claimed_origin, role, epoch):
        # Event-time driver; equivalent to repeated local_tick calls. Only the
        # bounded0..9 countdown is consumed by the provider's actual local rule.
        assert tick >= self.model_time
        elapsed = tick-self.model_time
        self.remaining = {o: max(0,r-elapsed) for o,r in self.remaining.items()}
        self.model_time = tick
        # Report authority cannot inhabit the physical request-origin role.
        if role != 'request' or physical_origin not in self.origins or claimed_origin != physical_origin:
            return False
        if epoch not in (0,1) or self.remaining[physical_origin] > 0:
            return False
        self.remaining[physical_origin] = 9
        return True


FRAME = tuple((F(a), F(b)) for a, b in
              [(1,0),(0,1),(1,1),(1,-1),(1,2),(2,1),(1,-2),(2,-1)])
MAP_A = tuple(frozenset([0 if i == 1 else i]) for i in range(8))
MAP_B = tuple(frozenset([2 if i == 3 else i]) for i in range(8))


def checks():
    tests = {}
    family = maximal_sets(domain_family((MAP_A, MAP_B), 2))
    assert pair_condition(FRAME, family) <= 3
    tests['domain_frame'] = {'rows': 8, 'maps': 2, 'bad_domains': 2,
                             'maximal_explanations': len(family), 'kappa_inf_certified': '3', 'kappa_best_pair_exact': str(pair_condition(FRAME, family)),
                             'max_deleted_rows': max(map(len, family))}
    # Independent geometric spec, genuine arbitrary Byzantine values, omission,
    # different receiver views, unknown map and exact lower-dimensional cases.
    cases = 0
    max_ops = max_bits = 0
    states = [(F(0), F(0)), (F(1, 3), F(-2, 5)), (F(-1, 2), F(1, 2))]
    for x in states:
        for actual in (family[0], family[-1], family[len(family)//2]):
            for attack in (F(-4), F(0), F(4), None):
                reports = [dot(h, x) + (F(1,100) if i % 2 else F(-1,100)) for i,h in enumerate(FRAME)]
                for i in actual:
                    reports[i] = attack
                beta = [F(1, 100)]*8
                result = decode(FRAME, reports, beta, family)
                assert result['bounds'] == spec_decode(FRAME, reports, beta, family)
                assert candidate_membership(FRAME, reports, beta, family, x)
                assert result['midpoint'] is not None
                assert max(abs(result['midpoint'][k]-x[k]) for k in range(2)) <= F(3,100)
                assert result['integer_ops'] <= result['kernel_op_bound']
                assert result['integer_bits'] <= result['kernel_bit_bound']
                max_ops = max(max_ops, result['integer_ops'])
                max_bits = max(max_bits, result['integer_bits'])
                cases += 1
    for reports in ([F(0)]*8, [dot(h, (F(1,3),F(-1,4))) for h in FRAME]):
        result = decode(FRAME, reports, [F(0)]*8, family)
        assert result['bounds'] == spec_decode(FRAME, reports, [F(0)]*8, family)
        assert result['bounds'][0] == result['bounds'][1]
        assert result['bounds'][2] == result['bounds'][3]
        cases += 1
    tests['exact_polygon'] = {'cases': cases, 'independent_spec': 'sequential rational half-plane clipping',
                              'max_observed_kernel_ops': max_ops, 'max_observed_integer_bits': max_bits,
                              'empty_and_lower_dimension_tested': True}
    assert decode(FRAME, [None]*8, [F(0)]*8, family)['bounds'] is None
    # A segment, point, and contradictory polytope; tests independent of strips.
    polygons = [
        [(F(1),F(0),F(0)),(F(-1),F(0),F(0)),(F(0),F(1),F(1)),(F(0),F(-1),F(1))],
        [(F(1),F(0),F(0)),(F(-1),F(0),F(0)),(F(0),F(1),F(0)),(F(0),F(-1),F(0))],
        [(F(1),F(0),F(-1)),(F(-1),F(0),F(-1)),(F(0),F(1),F(1)),(F(0),F(-1),F(1))]]
    for cs in polygons:
        raw = vertices_exact(cs)
        clipping = clip_polygon(cs)
        assert bool(raw) == bool(clipping)
        if raw:
            p1 = {(F(x,d),F(y,d)) for x,y,d in raw}
            p2 = set(clipping)
            assert p1 == p2
    # Independent exhaustive finite median spec, including all positions/values
    # of up to q Byzantine rows. Honest rows occupy both edges of the interval.
    median_cases = 0
    for q in range(3):
        m = 2*q+1
        for bad in all_subsets(range(m), q):
            good = [i for i in range(m) if i not in bad]
            for honest in product((F(2,5), F(3,5)), repeat=len(good)):
                for attacks in product((F(-9), None, F(9)), repeat=len(bad)):
                    vals = [None]*m
                    for i,v in zip(good,honest): vals[i] = v
                    for i,v in zip(bad,attacks): vals[i] = v
                    med, comparisons, shifts = median_group(vals)
                    expected = sorted(F(0) if v is None else v for v in vals)[q]
                    assert med == expected and F(2,5) <= med <= F(3,5)
                    assert comparisons <= m*(m-1)//2 and shifts <= m*(m-1)//2
                    median_cases += 1
    # Same truth, simultaneous equivocation to recipients; agreement unnecessary.
    q = 10
    m = 2*q+1
    first = [F(-4)]*q + [F(499,1000)]*(q+1)
    second = [F(4)]*q + [F(501,1000)]*(q+1)
    a, ac, ash = median_group(first)
    b, bc, bsh = median_group(second)
    assert a != b and abs(a-F(1,2)) <= F(1,1000) and abs(b-F(1,2)) <= F(1,1000)
    tests['coordinate_median'] = {'exhaustive_small_cases': median_cases,
                                  'large_case_bad_rows_per_group': q, 'rows_per_group': m,
                                  'recipient_estimates': [str(a),str(b)],
                                  'comparison_bound_per_group': m*(m-1)//2}
    # Counterexample to instantaneous counting: poison distinct rows at distinct
    # acquisition times, retain those reports, then fuse after current access ends.
    mobile_batch = [F(1), F(1), F(0)]
    assert median_group(mobile_batch)[0] == 1
    tests['instantaneous_count_counterexample'] = {'instantaneous_bad': 1,
                                                  'batch_bad_union': 2,
                                                  'truth': '0', 'median': '1'}
    # Per-true-map identifiability does not imply uniform identifiability.
    tiny_rows = ((F(1),F(0)), (F(1),F(0)), (F(0),F(1)))
    per_map_a = (frozenset([0]),)
    per_map_b = (frozenset([1]),)
    assert pair_condition(tiny_rows, per_map_a) is not None
    assert pair_condition(tiny_rows, per_map_b) is not None
    assert pair_condition(tiny_rows, per_map_a+per_map_b) is None
    reports = [F(0),F(1),F(0)]
    assert candidate_membership(tiny_rows,reports,[F(0)]*3,per_map_a+per_map_b,(F(0),F(0)))
    assert candidate_membership(tiny_rows,reports,[F(0)]*3,per_map_a+per_map_b,(F(1),F(0)))
    tests['hidden_map_counterexample'] = 'both individual map families identify; their union does not'
    # Nominal model coefficient cannot be substituted without widening.
    true_x, true_h, nominal_h = F(1), F(11,10), F(1)
    raw = true_h*true_x
    assert abs(nominal_h*true_x-raw) == F(1,10)
    tests['calibration_counterexample'] = 'zero widening excludes truth; mu=1/10 restores it'
    records = [(1,0,0,10,F(7)), (1,0,1,1000,F(1)), (2,0,1,10,F(1,2)),
               (3,0,1,10,F(-1)), (7,1,1,10,F(1,3)), (3,2,1,10,F(0))]
    accepted, work = admit(records,epoch=1,rows=2,start=0,close=5,max_length=64,max_value=F(4))
    assert accepted == [F(1,2),None]
    assert work <= len(records)*6 + 2*64
    tests['admission'] = {'accepted': [str(v) if v is not None else None for v in accepted],
                          'work':work, 'old_epoch_long_duplicate_late_bad_slot_checked':True}
    # Derived error and schedule arithmetic, no floating point.
    delta, drift, nonage, age, effect = F(1,1000), F(213,100), F(1,500), 20, 4
    eta = nonage + delta*drift*age
    effect_eta = eta + delta*drift*effect
    assert eta == F(223,5000) and effect_eta == F(166,3125)
    assert effect_eta + F(1,1000) < F(3,50)
    for q in (2,9,16,32):
        count = 2*(2*q+1)
        assert count == 4*q+2
    for tick in range(8,200):
        last_round = ((tick-8)//10)*10
        # Earliest admitted intact sample is round start+1.
        assert tick-(last_round+1) <= 16
    tests['main_interface'] = {'q':10,'total_rows_per_recipient':42,'round_period_ticks':10,
                               'publish_offset_ticks':8,'maximum_steady_sample_age_ticks':16,
                               'conservative_age_ticks':age,'first_post_reset_publish_ticks':20,
                               'noise_calibration_quantization_sum':str(nonage),
                               'delta':str(delta),'drift_factor':str(drift),
                               'current_error':str(eta),'after_four_effect_ticks':str(effect_eta),
                               'after_state_equivalent_rounding':str(effect_eta+F(1,1000)),
                               'receiver_ingress_bits_per_tick':1024,
                               'receiver_bounded_operations_per_tick':20000,
                               'round_work_bound':100000,'nominal_round_cost_per_recipient':220,
                               'all_requesters_interval_rate_per_recipient':25,
                               'all_requesters_interval_burst_per_recipient':500,
                               'n13_interval_rate':325,'n13_interval_burst':6500,
                               'complete_rogue_inquiry_footprint_power':72}
    quota = QueryQuota(range(13))
    assert not quota.accept(0, 0, 0, 'report', 0)
    assert not quota.accept(0, 1, 0, 'request', 0)
    assert not quota.accept(0, 0, 0, 'request', 10**100)  # no max-epoch poisoning
    accepted = [t for t in range(180) if quota.accept(t, 0, 0, 'request', t % 2)]
    assert all(b-a >= 9 for a,b in zip(accepted,accepted[1:]))
    assert all(0 <= r <= 9 for r in quota.remaining.values())
    for begin in range(120):
        for length in range(1,40):
            intersecting = sum(s < begin+length and s+8 > begin for s in accepted)
            assert intersecting <= F(length,9)+2
    reset_case = QueryQuota([0])
    assert reset_case.accept(0,0,0,'request',0)
    assert not reset_case.accept(8,0,0,'request',0)
    assert reset_case.accept(12,0,0,'request',0)  # same label after live window expires
    honest = QueryQuota([0])
    for k in range(30):
        assert honest.accept(10*k+1+k%2,0,0,'request',k%2)
    for value in (-4000,-1,0,1,4000):
        word=fixed_packet(41,1,value)
        assert parse_packet(word,41,1,42)==value
        assert parse_packet(word,40,1,42) is None
        assert parse_packet(word,41,0,42) is None
        assert parse_packet(word | (1<<40),41,1,42) is None
    # Saved valid reports defeat the bit scheme if a public injection path is
    # incorrectly left outside the effective bad-row/capability family.
    saved = [fixed_packet(i,0,1000) for i in range(3)]
    replayed = [F(parse_packet(word,i,0,3),1000) for i,word in enumerate(saved)]
    assert median_group(replayed)[0] == 1  # current truth may instead be0
    tests['uncharged_public_replay_counterexample'] = {
        'old_truth':'1','current_truth':'0','replayed_median':'1',
        'epoch_bit_matches_after_wrap':True,
        'conclusion':'origin authentication and bit/drain alone do not prevent public replay'}
    assert 42*64 <= 3*1024 and 13*64 <= 1024
    assert 8*1024+1000 < 10000
    assert F(210,9)+1 <=25 and 420<=500
    assert 2*(2*5+1024//64+1)+(1024//64+2)==72
    tests['query_quota_and_packet']={'malicious_accepted_jobs':len(accepted),
                                    'exhaustive_interval_checks':120*39,
                                    'honest_jittered_requests':30,
                                    'report_role_cannot_claim_request_origin':True,
                                    'fixed_word_packet_cases':20,
                                    'sample_batching_replies_per_tick':13}
    root=Path(__file__).parent
    sources={name:hashlib.sha256((root/name).read_bytes().replace(b'\r\n',b'\n')).hexdigest()
             for name in ('information_model.py','INFORMATION.md','Information.lean')}
    return {'status':'passed','scope':'finite executable checks; analytic general proofs in INFORMATION.md',
            'sources_sha256_lf':sources,'tests':tests}


def run_checks():
    return checks()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--check',action='store_true')
    parser.add_argument('--write-results',action='store_true')
    args = parser.parse_args()
    result = checks()
    if args.check:
        expected=Path(__file__).with_name('information_results.json')
        assert expected.exists(), 'No checked report; generate only after reviewed changes'
        assert json.loads(expected.read_text(encoding='utf-8')) == result, 'Source/results mismatch'
    if args.write_results:
        Path(__file__).with_name('information_results.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,indent=2))


if __name__ == '__main__':
    main()
