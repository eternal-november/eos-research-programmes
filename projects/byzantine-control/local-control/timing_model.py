"""Exact timing certificates and bounded adapter checks; not a pulser implementation."""
from __future__ import annotations

import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations, product
import json
from math import ceil, lcm
from pathlib import Path
import sys

if sys.flags.optimize:
    raise RuntimeError("Run without optimization: checks use assert")

HERE = Path(__file__).resolve().parent
THETA = F(1000001, 1000000)
PHI = F(1001, 1000)


def encoded(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encoded(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [encoded(v) for v in value]
    return value


def pulser_certificate(n: int, f: int, period: F, delay=F(1)):
    """Instantiate LR Tables 2--4; see TIMING.md for the import obligations.

    The imported machines, not this parameter checker, establish convergence.
    period and PHI*period are advertised conservative accuracy bounds.
    """
    assert n > 3*f and period > 0 and delay > 0
    h, phi, d = THETA, PHI, delay
    sigma = 2*d
    if f == 0:
        leader_timeout = h*(period+d)
        assert leader_timeout/h-d >= period
        assert leader_timeout+d <= phi*period
        return dict(n=n, f=f, minimum=period, maximum=phi*period,
                    stabilization=leader_timeout+2*d, sigma=sigma,
                    timeouts=[leader_timeout], children=[], checks=2,
                    mechanism="bounded leader timer inside a zero-fault recursive block")

    # n parallel OM(f) broadcasts + majority: f+1 rounds; silent wrapper: +2.
    rounds = f+3
    rho = h*(sigma+2*d)
    t1 = 3*h*d
    listen = (h-1)*t1+3*h*d
    t2 = h*(period+2*d)
    active = 6*t2
    tau = max((1-1/h)*t2+listen+d+max(listen+d, 3*t1+2*d),
              (1-1/h)*active+rho)

    # Section 4 initialized pulser, with deliberately roomy round gaps.
    p0 = h*(tau+d)
    p1 = h*((1-1/h)*p0+tau)
    p2 = 100*h*d
    p3 = h*((1-1/h)*p2+2*d)
    pgap = p2+p3+5*d
    simulation = p0+p1+3*d+(rounds+1)*pgap
    consensus = h*(tau+simulation)
    wait = t2+consensus
    main_checks = [
        p0/h >= tau+d, p1/h >= (1-1/h)*p0+tau,
        p2/h >= 3*d, p3/h >= (1-1/h)*p2+2*d,
        t2 > h*(listen+3*t1+3*d),
        (2/h-1)*t2 > 2*listen+consensus+5*t1+4*d,
        active >= 4*t2+listen+h*(listen+wait-5*t1-4*d+rho),
        active >= 2*t2+consensus+h*(2*listen+t1+wait+3*d+2*t2+2*consensus),
        (t2+consensus)/h+2*d <= phi*period,
    ]
    assert all(main_checks), (n, f, main_checks)
    # Explicit internal message-round offsets; source has processing inside d.
    send, receive = 4*h*d, 10*h*d
    low_gap = (p2+p3)/h-2*d
    assert send/h > sigma
    assert receive/h > sigma+send+d
    assert low_gap > sigma+send+d
    assert low_gap+send/h > sigma+receive
    assert low_gap > receive

    # Section 6 resynchronizer, with a gap exceeding the entire main recovery.
    psi = 10*t2
    assert psi > active+rho+consensus+2*d
    x = psi/(F(2, 25)*h*phi)
    beta = 3*psi
    cool = 16*h*beta
    periods = [x, F(31, 25)*x]
    children = [pulser_certificate(n//2, (f-1)//2, periods[0], d),
                pulser_certificate(n-n//2, f//2, periods[1], d)]
    vote = rho
    idle = h*(sigma+d)
    attention = h*(vote+2*d)
    resync_checks = []
    for p, count in zip(periods, (4, 5)):
        minimum, maximum = p-rho, h*(phi*p+vote)
        lo, hi = minimum/h, maximum+vote
        resync_checks += [p > psi+2*rho,
                          p >= vote+idle+attention+sigma+2*d,
                          minimum < cool, minimum/h > psi+rho,
                          cool/h > 15*beta,
                          beta > 2*psi+4*(vote+d)+rho]
        for j in range(4):
            resync_checks += [beta*count*j <= j*lo,
                              j*lo < j*hi+rho,
                              j*hi+rho <= beta*(count*j+1)]
    assert all(resync_checks), (n, f, resync_checks)
    tstar = max(ch["stabilization"]+2*ch["maximum"] for ch in children)+cool+sigma+2*d+rho
    # Lemma20 and I_1(11) in Lemma23; then Corollaries4--6.
    resync = tstar+max(ch["maximum"] for ch in children)+rho+2*(vote+d)+psi+11*beta
    stabilization = resync+active+rho+consensus+2*d
    local_timers = [p0,p1,p2,p3,t1,listen,t2,active,tau,consensus,wait,
                    psi,beta,cool,vote,idle,attention,send,receive]
    local_timers += [p-rho for p in periods]+[h*(phi*p+vote) for p in periods]
    return dict(n=n,f=f,minimum=period,maximum=phi*period,sigma=sigma,
                stabilization=stabilization,rounds=rounds,simulation=simulation,
                resynchronization=resync,main_recovery=active+rho+consensus+2*d,
                timeouts=local_timers,children=children,
                checks=len(main_checks)+5+1+len(resync_checks)+sum(ch["checks"] for ch in children),
                mechanism="LR2019 Figures4/5/10/11, recursive zero-fault leaves, silent OM consensus")


def counter_round_bound(f: int):
    """Conservative explicit bound from LRS Lemmas6--8 and phase-king closure."""
    if f == 0:
        return 1
    tau = 3*(f+2)
    return max(counter_round_bound((f-1)//2), counter_round_bound(f//2))+31*tau+4


def all_timers(cert):
    out = list(cert["timeouts"])
    for child in cert["children"]:
        out += all_timers(child)
    return out


def certificate_summary(cert):
    ts = all_timers(cert)
    denominator = lcm(*(v.denominator for v in ts))
    maximum = max(v*denominator for v in ts)
    assert maximum.denominator == 1
    return dict(n=cert["n"],f=cert["f"],minimum=cert["minimum"],maximum=cert["maximum"],
                stabilization=cert["stabilization"],stabilization_ceiling=ceil(cert["stabilization"]),
                counter_rounds=counter_round_bound(cert["f"]),
                timeout_quantum=F(1,denominator),max_timer_register_bits=maximum.numerator.bit_length(),
                parameter_inequalities_checked=cert["checks"],
                note="Exact rational alarm thresholds; no proof for an independently jittered timer implementation")


def round_adapter_checks():
    """Endpoint enumeration across skew, variable rate and invocation lag."""
    a,b,sigma,jitter,delay = F(1),F(101,100),F(2),F(1,10),F(1)
    send,receive,period = F(4),F(10),F(100)
    assert send/b > sigma
    assert receive/b > sigma+send/a+2*jitter+delay
    assert period > sigma+send/a+2*jitter+delay
    assert period+send/b > sigma+receive/a+jitter
    assert period > receive/a+jitter
    cases = 0
    for pi,pj,rate_s,rate_r,lag_s,lag_r,delivery in product(
            (F(0),sigma),(F(0),sigma),(a,b),(a,b),(F(0),jitter),(F(0),jitter),(F(0),delay)):
        sent = pj+send/rate_s+lag_s
        arrives = sent+delivery+lag_r
        consume_earliest = pi+receive/b
        consume_latest = pi+receive/a+jitter
        assert sent > pi
        assert arrives < consume_earliest
        assert arrives-period < pi
        assert sent+period > consume_latest
        cases += 1
    return dict(cases=cases,parameters=locals_subset(a=a,b=b,sigma=sigma,jitter=jitter,
        delay=delay,send=send,receive=receive,period=period),
        scope="Independent round-adapter interface test; the full pulser certificate uses THETA, not b=1.01")


def locals_subset(**kwargs):
    return kwargs


def chart_checks():
    """A genuine moving-cohort trace and separate exhaustive arithmetic tests.

    Generated pulse traces are inputs satisfying the chart interface. This does
    not simulate, implement, or verify the imported pulser or counting algorithm.
    """
    n,f,c,sigma = 7,2,15,2
    times = {(i,k):100*k+(i+3*k)%3 for i in range(n) for k in range(160)}
    q=102+4*sigma+1
    stride=4*q
    suffix=7*q
    # Each neighboring chart has a different omitted pair; no lifetime-clean member.
    cohorts = [set(range(n))-{j%n,(j+1)%n} for j in range(14)]
    assert not set.intersection(*cohorts)
    # Every participant has an actually extra event, but never inside a chart
    # that covers that participant. This is an interface trace, not protocol simulation.
    bad_events=[]
    for actor in range(n):
        first_omission=(actor-1)%n
        t=F((first_omission-1)*stride+suffix+(first_omission+2)*stride,2)
        for j,cohort in enumerate(cohorts):
            assert actor not in cohort or not j*stride<=t<=j*stride+suffix
        bad_events.append(dict(actor=actor,time=t,label="arbitrary-extra"))
    anchors=[]
    for j in range(13):
        shared=min(cohorts[j]&cohorts[j+1])
        cut=(j+1)*stride+sigma
        k=next(k for k in range(160) if times[shared,k]>=cut)
        anchors.append((shared,k,times[shared,k]))
    assert all(anchors[j+1][2]>anchors[j][2] for j in range(12))
    groups=[]
    for k in range(anchors[0][1],anchors[-1][1]+1):
        boundary=next((j for j,a in enumerate(anchors) if a[1]==k),None)
        if boundary is not None:
            nodes=cohorts[boundary]|cohorts[boundary+1]
        else:
            owner=next(j+1 for j in range(12) if anchors[j][1]<k<anchors[j+1][1])
            nodes=cohorts[owner]
        values=[times[i,k] for i in nodes]
        assert len(nodes)>=n-f and max(values)-min(values)<=2*sigma
        groups.append((k,min(values),max(values),(k+7)%c))
    for x,y in zip(groups,groups[1:]):
        assert 98-2*sigma<=y[1]-x[1]<=102+2*sigma
        assert y[3]==(x[3]+1)%c
    arithmetic=0
    for s in range(4):
        for anchor in range(8):
            for left,right in product(range(anchor-s,anchor+s+1),repeat=2):
                assert abs(left-right)<=2*s
                arithmetic+=1
    intersects=0
    for left,right in product(list(combinations(range(n),n-f)),repeat=2):
        assert len(set(left)&set(right))>=n-2*f
        intersects+=1
    # Same finite label is insufficient to match an event: wrap is not identity.
    assert (1%c)==((1+c)%c) and times[0,1]!=times[0,1+c]
    return dict(n=n,f=f,cohorts=[sorted(x) for x in cohorts],
                lifetime_clean_intersection=[],anchors=anchors,extra_fault_events=bad_events,
                chart_stride=stride,trusted_suffix_length=suffix,
                checked_groups=len(groups),pairwise_cohort_cases=intersects,
                anchor_arithmetic_cases=arithmetic,
                same_label_different_events=[times[0,1],times[0,1+c]])


def schedule_checks():
    cases=0
    for tasks,block in product(range(1,10),range(3,12)):
        modulus=tasks*block
        for start in range(modulus):
            word=[(start+k)%modulus for k in range(modulus)]
            for task in range(tasks):
                offsets=[k for k,z in enumerate(word) if z//block==task and z%block==1]
                assert len(offsets)==1 and 0<=offsets[0]<modulus
            assert len({(z//block,z%block) for z in word})==modulus
            cases+=1
    return dict(start_states=cases,decoder="task=z//B, phase=z%B, c=B*M")


def shutdown_cover_obstruction(history_window, period):
    shutdowns=[(i, i*10*period) for i in range(7)]
    assert shutdowns[-1][1] < history_window
    cover={actor for actor,t in shutdowns if 0<=t<=history_window}
    assert len(cover)==7>2
    return dict(n=7,f=2,shutdowns=shutdowns,covered=sorted(cover),
                verdict="Cyclic shutdown of every scheduler within W violates this adapter's window cover")


def lease_split():
    # Fixed fast/slow routes reproduce this behavior every lease cycle.
    history=[]
    for cycle in range(8):
        expiry=cycle*12+10
        grants={"g0":"A","g1":"A","g2":"B","g3":"B"}
        assert sum(x=="A" for x in grants.values())==2<3
        assert sum(x=="B" for x in grants.values())==2<3
        history.append(dict(cycle=cycle,grants=grants,expiry=expiry,completed=[]))
    return dict(quorum=3,guardians=4,nominal_message_delay_bound=1,
                fast_request_delay=F(1,4),slow_request_delay=F(3,4),
                lease=10,drain=2,cycles=history,
                witness="finite prefix of the same periodic infinite split schedule")


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    group=parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--write",action="store_true")
    group.add_argument("--check",action="store_true")
    args=parser.parse_args()
    names=("TIMING.md","Timing.lean","timing_model.py")
    hashes={name:sha256((HERE/name).read_bytes().replace(b"\r\n",b"\n")).hexdigest() for name in names}
    certs=[pulser_certificate(3*f+1,f,F(10**6*(f+1))) for f in range(1,5)]
    sample=certs[1]
    pmax=sample["maximum"]
    startup=sample["stabilization"]+(counter_round_bound(2)+3)*pmax+20
    q=pmax+4*sample["sigma"]+1
    record=dict(status="passed",scope="rational imported-parameter certificates and finite adapter/atlas checks; not full source admission",
                sources_sha256_lf=hashes,theta=THETA,phi=PHI,
                pulser_certificates=[certificate_summary(v) for v in certs],
                sample=dict(n=7,f=2,startup_ceiling=ceil(startup),
                            chart_stride=4*q,suffix_length=7*q,history_window=startup+7*q,
                            maturity_wait_real=startup+7*q),
                round_adapter=round_adapter_checks(),chart_checks=chart_checks(),
                scheduler=schedule_checks(),lease_split=lease_split(),
                shutdown_cover_obstruction=shutdown_cover_obstruction(startup+7*q,sample["minimum"]),
                residuals=["imported full algorithm proofs are not reconstructed",
                    "source realization of timer semantics, bounded virtual links, work and code restoration",
                    "independent review of explicit import constants and event-splice proof",
                    "physical startup service, permission, release and useful completion"])
    text=json.dumps(encoded(record),sort_keys=True,indent=2)+"\n"
    path=HERE/"timing_results.json"
    if args.write:
        path.write_text(text,encoding="utf-8",newline="\n")
    else:
        assert path.read_text(encoding="utf-8")==text,"Timing record differs"
    print(json.dumps(dict(status="passed",certificates=len(certs),
                         inequalities=sum(x["checks"] for x in certs),
                         scheduler_starts=record["scheduler"]["start_states"],
                         groups=record["chart_checks"]["checked_groups"])))


if __name__=="__main__":
    main()
