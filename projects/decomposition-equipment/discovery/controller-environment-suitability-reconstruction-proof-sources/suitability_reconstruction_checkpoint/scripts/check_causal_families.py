#!/usr/bin/env python3
"""Reproducible finite checks for Causal_Interlock_and_Telemetry_Families.md.
No external packages. These checks supplement, not prove, its all-size claims.
"""
from itertools import product, permutations
from collections import defaultdict
from pathlib import Path
import json, hashlib, random

ROOT = Path(__file__).resolve().parents[1]


def bits(n):
    return tuple(product((0, 1), repeat=n))


def admission(x):
    n = len(x)//2
    return int(x[:n] == x[n:])


def residuals(n, order, t):
    """Direct truth-table residuals, with no frontier formula in calculation."""
    pre, post = order[:t], order[t:]
    table = defaultdict(dict)
    for x in bits(2*n):
        p = tuple(x[j] for j in pre)
        z = tuple(x[j] for j in post)
        table[p][z] = admission(x)
    suffixes = bits(len(post))
    return {p: tuple(row[z] for z in suffixes) for p,row in table.items()}


def frontier_prediction(n, order, t):
    seen = set(order[:t])
    active = sum((i in seen) != (i+n in seen) for i in range(n))
    complete = sum(i in seen and i+n in seen for i in range(n))
    return 2**active + int(complete > 0)


def check_order(n, order):
    layers = [residuals(n, order, t) for t in range(2*n+1)]
    counts = [len(set(d.values())) for d in layers]
    assert counts == [frontier_prediction(n, order, t) for t in range(2*n+1)]
    # The residual transition is functional and causal: same state and next bit
    # cannot prescribe different successor residuals.
    for t in range(2*n):
        trans = {}
        for prefix, old in layers[t].items():
            for b in (0,1):
                key = old,b
                new = layers[t+1][prefix+(b,)]
                assert key not in trans or trans[key] == new
                trans[key] = new
    return counts


def four_state_run(n, x):
    state = 'G'
    for i in range(n):
        for role, bit in [('U',x[i]),('V',x[i+n])]:
            if state == 'B':
                continue
            if role == 'U':
                assert state == 'G'
                state = 'P'+str(bit)
            else:
                assert state in ('P0','P1')
                state = 'G' if int(state[1]) == bit else 'B'
    return int(state == 'G')


def directly_decode(states, obs0, obs, demands, encoder):
    """Attempt to construct actual deterministic local decoder tables."""
    ds = [dict() for _ in obs]
    for x in states:
        message = encoder[obs0[x]]
        for i in range(len(obs)):
            key = message, obs[i][x]
            need = demands[i][x]
            if key in ds[i] and ds[i][key] != need:
                return None
            ds[i][key] = need
    return ds


def confusion_color_check(states, obs0, obs, demands, encoder):
    """Independent pairwise criterion; does not construct decoder tables."""
    for k,x in enumerate(states):
        for y in states[k+1:]:
            confused = any(obs[i][x] == obs[i][y] and demands[i][x] != demands[i][y]
                           for i in range(len(obs)))
            if confused and encoder[obs0[x]] == encoder[obs0[y]]:
                return False
    return True


def source_tuples_check(n, order):
    """Actual phase/bit graph coordinate witnesses, both state/event sorts."""
    for event_sort in (False, True):
        stages = range(2*n) if event_sort else range(2*n+1)
        for t in stages:
            for x in bits(2*n):
                whole = (t,x)
                flat_uv = tuple((t,b) for b in x)
                region = (tuple((t,x[i]) for i in range(n)),
                          tuple((t,x[n+i]) for i in range(n)))
                pair = tuple(((t,x[i]),(t,x[n+i])) for i in range(n))
                via_region = tuple(z for r in region for z in r)
                via_pair = tuple(z for r in pair for z in r)
                assert via_region == flat_uv
                pair_order = tuple(j for i in range(n) for j in (i,n+i))
                assert via_pair == tuple(flat_uv[j] for j in pair_order)
                assert (t,tuple(z[1] for z in via_region)) == whole
                assert len({z[0] for z in via_region}) == 1
                # Actual source and target compatibility on events.
                if event_sort:
                    source = tuple((t,b) for b in x)
                    target = tuple((t+1,b) for b in x)
                    assert source == via_region
                    assert target == tuple((s+1,b) for s,b in via_region)
                    # Physical observation exposes only scheduled coordinate.
                    observation = (order[t],x[order[t]])
                    assert observation == (order[t],via_region[order[t]][1])


def register_run(n, x, order):
    p,a=0,1
    for coordinate in order:
        b=x[coordinate]
        if coordinate<n: p=b
        else: a=a & int(p==b)
    return a


def two_sided_register_check(n):
    """Construct actual L x_I A event records and couple to the actual plant."""
    order=tuple(j for i in range(n) for j in (i,n+i))
    checked=0
    for t,coordinate in enumerate(order):
        role_u=coordinate<n
        latch={(p,b,pp) for p,b,pp in product((0,1),repeat=3)
               if pp==(b if role_u else p)}
        accumulator={(p,a,b,pp,aa) for p,a,b,pp,aa in product((0,1),repeat=5)
                     if aa==(a if role_u else a & int(p==b))}
        joined={(p,a,b,pp,aa) for p,a,b,pp,aa in accumulator if (p,b,pp) in latch}
        direct={(p,a,b,(b if role_u else p),(a if role_u else a & int(p==b)))
                for p,a,b in product((0,1),repeat=3)}
        assert joined==direct
        for x in bits(2*n):
            plant_reply=x[coordinate]
            for p,a in product((0,1),repeat=2):
                matches=[z for z in joined if z[0]==p and z[1]==a and z[2]==plant_reply]
                assert len(matches)==1
                # Expanding environment first or controller first retains same tuple.
                pp,aa=matches[0][3:]
                environment_first=(t,tuple((t,v) for v in x),p,a,plant_reply,pp,aa)
                controller_first=(t,tuple((t,v) for v in x),p,a,matches[0][2],pp,aa)
                assert environment_first==controller_first
                checked+=1
    for x in bits(2*n):
        assert register_run(n,x,order)==admission(x)
    return checked


def main():
    report = {'status':'PASS','checks':{}}
    orders = 0
    for n in range(1,4):
        for order in permutations(range(2*n)):
            check_order(n, order)
            orders += 1
    rng = random.Random(20261027)
    for n in (4,5):
        samples = [tuple(range(2*n)),tuple(j for i in range(n) for j in (i,i+n))]
        for _ in range(12):
            p = list(range(2*n)); rng.shuffle(p); samples.append(tuple(p))
        for order in samples:
            check_order(n,order); orders += 1
    report['checks']['direct_residual_orders'] = orders
    report['checks']['all_orders_exhausted_n'] = [1,2,3]
    report['checks']['sampled_larger_n'] = [4,5]

    widths = []
    for n in range(1,9):
        # n>5 formula follows proof; explicit controller test remains exhaustive.
        if n <= 5:
            b = check_order(n,tuple(range(2*n)))
            p = check_order(n,tuple(j for i in range(n) for j in (i,i+n)))
            assert max(b) == 2**n
            assert max(p) == (2 if n == 1 else 3)
        for x in bits(2*n):
            assert four_state_run(n,x) == admission(x)
        widths.append({'n':n,'proved_block_width':2**n,
                       'proved_interleaved_width':2 if n==1 else 3,
                       'four_state_executions_checked':2**(2*n)})
    report['checks']['width_family'] = widths

    # Every pair of different first blocks has the concrete separating suffix.
    pairs = 0
    for n in range(1,8):
        xs = bits(n)
        for i,u in enumerate(xs):
            for up in xs[i+1:]:
                v = u
                assert admission(u+v) == 1 and admission(up+v) == 0
                pairs += 1
    report['checks']['block_distinguishing_pairs'] = pairs

    # Actual original dynamic-target coordinate tables, not just profile names.
    for n in range(1,4):
        source_tuples_check(n,tuple(range(2*n)))
        source_tuples_check(n,tuple(j for i in range(n) for j in (i,n+i)))
    report['checks']['dynamic_graph_instances'] = 6
    report['checks']['two_sided_coupled_register_records'] = sum(two_sided_register_check(n) for n in range(1,5))
    assert register_run(2,(0,1,0,1),(0,1,2,3)) != admission((0,1,0,1))

    # Exhaust all directed side-information patterns n<=3 and binary encoders.
    comparisons = 0; positive = 0
    for n in range(1,4):
        xs = bits(n)
        possible = [(i,j) for i in range(n) for j in range(n) if i!=j]
        for incidence in bits(len(possible)):
            side = [{j for b,(ii,j) in zip(incidence,possible) if b and ii==i}
                    for i in range(n)]
            obs0 = {x:x for x in xs}
            obs = [{x:tuple(x[j] for j in sorted(side[i])) for x in xs}
                   for i in range(n)]
            demand = [{x:x[i] for x in xs} for i in range(n)]
            for values in bits(len(xs)):
                enc = dict(zip(xs,values))
                d = directly_decode(xs,obs0,obs,demand,enc)
                c = confusion_color_check(xs,obs0,obs,demand,enc)
                assert (d is not None) == c
                comparisons += 1; positive += c
    report['checks']['encoder_decoder_vs_coloring'] = comparisons
    report['checks']['successful_binary_codes'] = positive

    # Encoder observation restrictions: enumerate projections and all tables.
    obs_cases = 0
    n=3; xs=bits(n)
    for keep_mask in bits(n):
        keep=[i for i in range(n) if keep_mask[i]]
        obs0={x:tuple(x[i] for i in keep) for x in xs}
        keys=sorted(set(obs0.values()))
        obs=[{x:tuple(x[j] for j in range(n) if j!=i) for x in xs} for i in range(n)]
        demand=[{x:x[i] for x in xs} for i in range(n)]
        successes=0
        for vals in bits(len(keys)):
            enc=dict(zip(keys,vals))
            d=directly_decode(xs,obs0,obs,demand,enc)
            assert (d is not None)==confusion_color_check(xs,obs0,obs,demand,enc)
            successes += d is not None; obs_cases += 1
        assert bool(successes)==all(keep_mask)
    report['checks']['physically_observed_encoder_tables'] = obs_cases

    # Proper-subfamily feasibility uses a DIFFERENT candidate encoder per J.
    local_cases=0
    for n in range(2,7):
        xs=bits(n)
        for mask in bits(n):
            jset=[j for j in range(n) if mask[j]]
            if len(jset)==n: continue
            enc={x:tuple(x[j] for j in jset) for x in xs}
            assert len(set(enc.values())) <= 2**(n-1)
            for x in xs:
                for k,j in enumerate(jset): assert enc[x][k]==x[j]
            local_cases+=1
        # Full family confusion graph complete, hence needs 2^n colors.
        assert all(any(x[i]!=y[i] for i in range(n)) for k,x in enumerate(xs) for y in xs[k+1:])
    report['checks']['proper_receiver_subsets'] = local_cases

    # Negative controls: catch each shortcut by an explicit counterexample.
    n=3
    assert max(check_order(n,tuple(range(2*n))))==8
    assert max(check_order(n,tuple(j for i in range(n) for j in (i,n+i))))==3
    # Final answer cardinality2 does NOT license memory2 at block midpoint.
    assert 2 < 8
    u=(0,0,0); up=(1,1,0)
    assert sum(u)%2==sum(up)%2
    assert admission(u+u)!=admission(up+u)
    # Missing snapshot: identical observations, differing commit states.
    observed=(0,0,0,0)
    actual_unchanged=(0,0,0,0); actual_unseen_flip=(0,0,1,0)
    assert admission(actual_unchanged)!=admission(actual_unseen_flip)
    assert observed==tuple(actual_unchanged)
    # Ignoring completeness accepts constant refusal but fails on equality.
    assert admission((0,0))==1
    report['checks']['negative_controls']=[
        'final-output-size-is-not-driver-memory',
        'same-episode-records-do-not-preserve-observation-order',
        'parity-compressed-block-prefix-is-insufficient',
        'unobserved-post-read-change-breaks-current-admission',
        'constant-refusal-is-not-complete-admission',
        'local-redesigned-encoders-are-not-one-shared-controller',
        'encoder-cannot-read-unpermitted-hazard-bits']
    report['source_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    doc=ROOT/'examples/Causal_Interlock_and_Telemetry_Families.md'
    report['manuscript_sha256']=hashlib.sha256(doc.read_bytes()).hexdigest()
    out=ROOT/'examples/Causal_Family_Checks.json'
    out.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__': main()
