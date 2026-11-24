"""Finite filtering and first-passage support risk. Python 3.12."""
import argparse
from fractions import Fraction as Q
from itertools import product
import json
from collections import defaultdict

S = tuple(product((0,1),repeat=2))
INIT = {s:Q(1,4) for s in S}
FLIP = Q(1,8)


def k(i,j):
    return FLIP if i!=j else 1-FLIP


def transition(s,t):
    return k(s[0],t[0])*k(s[1],t[1])


def weight(mode, law, z, s):
    i,j = s
    if mode == "split":
        u,v = z
        return k(i,u)*k(j,v)  # Independent reading errors.
    if mode == "plain":
        return Q(1,2)
    if mode == "reveal":
        report, local = z
        return int(i==local)*weight("shared",law,report,s)
    assert mode == "shared"
    miss = Q(3 if ((i==j)==(law=="+")) else 1,4)
    return miss if z=="missing" else 1-miss


def det(p):
    return p[(0,0)]*p[(1,1)]-p[(0,1)]*p[(1,0)]


def moments(p):
    return p[(1,0)]+p[(1,1)], p[(0,1)]+p[(1,1)], det(p)


def decode(u,v,d):
    return {(0,0):(1-u)*(1-v)+d,(0,1):(1-u)*v-d,
            (1,0):u*(1-v)-d,(1,1):u*v+d}


def normalize(m):
    z=sum(m.values())
    assert z
    return {s:x/z for s,x in m.items()},z


def predict(m):
    return {t:sum(m[s]*transition(s,t) for s in S) for t in S}


def update(prev, step, law):
    mode,event=step
    m=predict(prev)
    u,v,d = moments(prev)
    multiplier=1-2*FLIP
    packed = decode(FLIP+multiplier*u,FLIP+multiplier*v,multiplier**2*d)
    assert packed==m
    p,q=normalize({s:m[s]*weight(mode,law,event,s) for s in S})
    assert decode(*moments(p))==p
    return p,q


def posterior(history,law):
    p,prob=INIT,Q(1)
    for h in history:
        p,q=update(p,h,law)
        prob*=q
    return p,prob


def risk(p,windows=2):
    # Loss after the next shared dispatch windows, paid regardless of reports.
    # A killed vector retains actual pre-first-failure mass; never normalize.
    alive=dict(p)
    for _ in range(windows):
        alive=predict(alive)
        alive[1,1]=Q(0)
    return 1-sum(alive.values())


def exact_paths(history,law):
    """Separate world-path oracle: sum observation and failure events."""
    n=len(history)
    filtered=defaultdict(Q)
    event=fail=Q(0)
    for path in product(S,repeat=n+3):
        w=Q(1,4)
        for i,(s,t) in enumerate(zip(path,path[1:])):
            # Use bit persistence/count rather than transition() in the oracle.
            flips=sum(x!=y for x,y in zip(s,t))
            w*=FLIP**flips*(1-FLIP)**(2-flips)
            if i<n:
                mode,z=history[i]
                w*=weight(mode,law,z,t)
        event+=w
        filtered[path[n]]+=w
        if (1,1) in path[n+1:]:
            fail+=w
    return {s:filtered[s]/event for s in S},event,fail/event


def fmt(x):
    if isinstance(x,Q):
        return str(x)
    if isinstance(x,dict):
        return {k:fmt(v) for k,v in x.items()}
    if isinstance(x,(tuple,list)):
        return [fmt(y) for y in x]
    return x


def main():
    # Fixed public action policy: start shared, then retry shared only after
    # a missing outcome. Successful first receipt switches to plain sensing.
    q_hist=[(("shared",e),("shared" if e=="missing" else "plain",f))
            for e,f in product(("missing","received"),repeat=2)]
    allclaims={}
    for law in ("+","-"):
        records=[]
        mission=Q(0)
        for h in q_hist:
            p,w=posterior(h,law)
            rr=risk(p)
            assert exact_paths(h,law)==(p,w,rr)
            assert moments(p)[:2]==(Q(1,2),Q(1,2))
            d=moments(p)[2]
            next_hazard=predict(p)[1,1]
            assert next_hazard==Q(1,4)+Q(9,16)*d
            assert rr==Q(79,256)+Q(459,1024)*d
            records.append(dict(history=h,evidence_mass=w,certificate=moments(p),
                                next_hazard=next_hazard,risk=rr))
            mission+=w*rr
        assert sum(r["evidence_mass"] for r in records)==1
        assert mission==risk(INIT)==Q(79,256)
        allclaims[law]=records
    assert [r["evidence_mass"] for r in allclaims["+"]]==[r["evidence_mass"] for r in allclaims["-"]]
    one=allclaims["+"][0]
    other=allclaims["-"][0]
    naive=risk(INIT)
    assert one["risk"]>Q(1,3)>naive>other["risk"]
    # Independently factorized two-coordinate observations retain product form.
    split=[posterior((("split",z),("split",w)),"+")[0]
           for z,w in product(S,repeat=2)]
    assert all(det(p)==0 for p in split)
    # Full prior, rectangular sparse support, non-rectangular sparse support,
    # and impossible event retained distinctly.
    sparse = ({s:Q(int(s[0]==0)) for s in S},
              {s:Q(int(s[0]==s[1])) for s in S},
              {s:Q(0) for s in S})
    for l,expected in zip(sparse,(0,Q(1,4),None)):
        numerator={s:INIT[s]*l[s] for s in S}
        if expected is None:
            assert sum(numerator.values())==0
        else:
            assert det(normalize(numerator)[0])==expected
    # Timing/observational change: actual local-bit witness on second retry,
    # not imported ground truth. Its disclosure gives a point-mass first margin.
    reveal=[]
    for law in ("+","-"):
        p0,w0=posterior(q_hist[0],law)
        rs=[]
        for bit in (0,1):
            h=(("shared","missing"),("reveal",("missing",bit)))
            p,w=posterior(h,law)
            assert exact_paths(h,law)==(p,w,risk(p))
            assert det(p)==0 and moments(p)[0]==bit
            rs.append((w,risk(p)))
        assert sum(w for w,r in rs)==w0 and sum(w*r for w,r in rs)==w0*risk(p0)
        reveal.append(rs)
    # Survival after dispatch selects away the jointly failed cell. The
    # resulting dependence is unrelated to whether monitoring factored.
    survive,z=normalize({s:(Q(0) if s==(1,1) else INIT[s]) for s in S})
    assert det(survive)==-Q(1,9) and z==Q(3,4)
    assert 1-z+z*risk(survive,windows=1)==naive
    return fmt(dict(laws=allclaims,nominal_ex_ante=naive,product_at_decision_naive=naive,
                    late_local_bit_report=reveal,survival_mass=z,
                    survival_certificate=moments(survive),surviving_next_risk=risk(survive,1),
                    sharp_uniform_double_miss=max(one["risk"],other["risk"]),
                    uniform_double_miss_next_hazard=max(one["next_hazard"],other["next_hazard"]),
                    threshold_regression=Q(1,3)))


if __name__=="__main__":
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--json",action="store_true")
    out=main()
    if cli.parse_args().json:
        print(json.dumps(out,indent=2,sort_keys=True))
    else:
        print({k:v[0] for k,v in out["laws"].items()})
        print({k:v for k,v in out.items() if k!="laws"})
