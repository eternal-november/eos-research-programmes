#!/usr/bin/env python3
"""Exact finite end-to-end representation discovery on hypothetical data.

All computations use Python's standard library and rational/integer arithmetic.
The complete simultaneous confidence family consists of all 16 Boolean event
statistics on two flags.  No physical data were collected by this script.
"""
from fractions import Fraction as Q
from itertools import product, combinations
from math import comb
from pathlib import Path
import json

OMEGA = tuple(product((0, 1), repeat=2))
HIST = (240, 30, 30, 0)  # order00,01,10,11
N = sum(HIST)
D = 2000
ALPHA = Q(1, 50)
DELTA = Q(1, 20)
FUNCTIONS = tuple(product((0, 1), repeat=4))
HAZARD = (0, 0, 0, 1)
COUNTS = {f: sum(n*v for n,v in zip(HIST,f)) for f in FUNCTIONS}


def cdf_numerator(k, j):
    return sum(comb(N,i)*j**i*(D-j)**(N-i) for i in range(k+1))


def binomial_upper(k):
    """Outward grid rounding of one-sided CP upper endpoint at delta/16."""
    if k == N:
        return Q(1)
    lo, hi = 0, D
    while hi-lo > 1:
        mid = (lo+hi)//2
        if cdf_numerator(k,mid)*320 <= D**N:
            hi = mid
        else:
            lo = mid
    assert cdf_numerator(k,hi)*320 <= D**N
    assert hi == 0 or cdf_numerator(k,hi-1)*320 > D**N
    return Q(hi,D)

UPPER_BY_COUNT = {k:binomial_upper(k) for k in sorted(set(COUNTS.values()))}
UPPER = {f:UPPER_BY_COUNT[COUNTS[f]] for f in FUNCTIONS}
assert UPPER[HAZARD] == Q(39,2000) < ALPHA
assert Q(1961,2000)**300 < Q(1,320)


def solve_linear(rows, rhs):
    a = [[Q(x) for x in row]+[Q(y)] for row,y in zip(rows,rhs)]
    n=len(a)
    for c in range(n):
        pivot=next((r for r in range(c,n) if a[r][c]),None)
        if pivot is None:
            return None
        a[c],a[pivot]=a[pivot],a[c]
        q=a[c][c];a[c]=[x/q for x in a[c]]
        for r in range(n):
            if r != c:
                q=a[r][c]
                a[r]=[x-q*y for x,y in zip(a[r],a[c])]
    return tuple(row[-1] for row in a)


def maximize_risk(features):
    # Inequalities ap<=b include nonnegativity and every calibrated event row.
    constraints=[(tuple(-int(i==j) for i in range(4)),Q(0)) for j in range(4)]
    constraints += [(tuple(map(Q,f)),UPPER[f]) for f in sorted(set(features))]
    vertices=set()
    for active in combinations(constraints,3):
        v=solve_linear([(1,1,1,1)]+[a for a,b in active],[1]+[b for a,b in active])
        if v is not None and all(sum(x*y for x,y in zip(a,v))<=b for a,b in constraints):
            vertices.add(v)
    assert vertices, 'nonempty confidence set is required'
    witness=max(vertices,key=lambda p:p[3])
    assert sum(witness)==1 and min(witness)>=0
    return witness[3], witness, len(vertices)


def complement(f):
    return tuple(1-x for x in f)


def depends_on(f, coordinate):
    return all(f[i]==f[j] for i,a in enumerate(OMEGA) for j,b in enumerate(OMEGA)
               if a[coordinate]==b[coordinate])

LOCAL = tuple(f for f in FUNCTIONS if depends_on(f,0) or depends_on(f,1))
assert len(LOCAL)==6
LOCAL_RISK, LOCAL_WITNESS, LOCAL_VERTICES=maximize_risk(LOCAL)
assert LOCAL_RISK > ALPHA
# A transparent adverse coupling is feasible even with actual simultaneous CIs.
ADVERSE=(Q(9,10),Q(0),Q(0),Q(1,10))
assert all(sum(p*x for p,x in zip(ADVERSE,f))<=UPPER[f] for f in LOCAL)
assert ADVERSE[3] > ALPHA

# Unknown retained bit is selected by the exact risk check, not hard-coded.
results=[]
for f in FUNCTIONS:
    risk,witness,vertex_count=maximize_risk(LOCAL+(f,complement(f)))
    results.append((f,risk,witness,vertex_count))
successes=[r for r in results if r[1]<=ALPHA]
assert {r[0] for r in successes} == {HAZARD,complement(HAZARD)}
for f,risk,witness,_ in successes:
    assert risk==Q(39,2000)
    # Dual: hazard indicator itself is an available output event row.
    row = f if f==HAZARD else complement(f)
    assert row == HAZARD and all(row[i]>=HAZARD[i] for i in range(4))
    assert UPPER[row] == risk
# No added retained report is sufficient; one added bit is thus minimal here.
assert LOCAL_RISK > ALPHA and successes
assert maximize_risk((HAZARD,complement(HAZARD)))[0] == Q(39,2000)
assert LOCAL_WITNESS[3] > UPPER[HAZARD]  # unused row refutes this countermodel


def execute_encoder_decoder(encoder, decoder, x, y):
    # Phase0 A sees x; phase1 message arrives B; B then reads own y/decodes.
    msg=encoder[x]
    return decoder[2*msg+y]


def synthesize_distributed(f, message_symbols):
    programs=[]
    for enc in product(range(message_symbols),repeat=2):
        for dec in product((0,1),repeat=2*message_symbols):
            if tuple(execute_encoder_decoder(enc,dec,x,y) for x,y in OMEGA)==f:
                programs.append((enc,dec))
    return programs

PROGRAM_COUNTS={}
for f in FUNCTIONS:
    for k in (1,2):
        progs=synthesize_distributed(f,k)
        PROGRAM_COUNTS[(f,k)]=len(progs)
        assert bool(progs) == (k==2 or depends_on(f,1))
for f,_,_,_ in successes:
    assert not synthesize_distributed(f,1)
    assert synthesize_distributed(f,2)

# Existing-data eligibility is a separate condition from executable-program search.
def eligible_existing_rows(aligned):
    return FUNCTIONS if aligned else LOCAL

assert HAZARD in eligible_existing_rows(True)
assert HAZARD not in eligible_existing_rows(False)
UNALIGNED_RISK,_,_=maximize_risk(eligible_existing_rows(False))
assert UNALIGNED_RISK==LOCAL_RISK
# Population-level necessity: same complete one-flag marginals, opposite hazard risk.
SAFE=(Q(4,5),Q(1,10),Q(1,10),Q(0))
assert all(sum(p*x for p,x in zip(SAFE,f))==sum(p*x for p,x in zip(ADVERSE,f)) for f in LOCAL)
assert SAFE[3]==0 and ADVERSE[3]==Q(1,10)

out={
 'status':'PASS',
 'data':'constructed validation histogram, not collected robot data',
 'histogram':list(HIST),'sample_size':N,
 'confidence_failure_budget':str(DELTA),'simultaneous_event_functions':len(FUNCTIONS),
 'confidence_method':'one-sided exact binomial inversion, rounded upward to denominator2000',
 'upper_bounds_by_count':{str(k):str(v) for k,v in UPPER_BY_COUNT.items()},
 'local_event_functions':len(LOCAL),'local_robust_risk':str(LOCAL_RISK),
 'local_adverse_optimizer':[str(x) for x in LOCAL_WITNESS],
 'searched_one_bit_reports':len(results),'successful_report_tables':[list(r[0]) for r in successes],
 'certified_risk':str(successes[0][1]),'risk_budget':str(ALPHA),
 'minimum_added_retained_report_bits':1,
 'future_distributed_program':'one A-to-B bit necessary and sufficient for selected report',
 'encoder_decoder_searches':len(PROGRAM_COUNTS),
 'encoder_decoder_table_pairs_tested':16*(4+64),
 'streaming_event_counter_bits':9,
 'existing_unaligned_logs_gain_no_joint_row':True,
 'population_identical_marginal_pair_risks':[str(SAFE[3]),str(ADVERSE[3])],
 'scope':'finite source-program/statistic search, exact LP and certificate check; no physical validation'
}
print(json.dumps(out,indent=2))
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
