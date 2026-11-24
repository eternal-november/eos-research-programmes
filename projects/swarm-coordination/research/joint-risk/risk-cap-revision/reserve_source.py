"""Two mandatory dispatches; robust protection with zero or one parity bit."""
import argparse
from fractions import Fraction as Q
from itertools import product
import json

STATES = tuple(product((0,1),repeat=2))
WORDS = tuple(product(("miss","got"),repeat=2))
LAWS = ("plus","minus")
LOSS = {3:(1,1),4:(1,0)}
FLIP = Q(1,8)
LAM = Q(9,16)
LIMIT = Q(1,5)


def local_transition(a,b):
    return FLIP if a != b else 1-FLIP


def path_likelihood(law,word,path):
    """Same fixed sensing policy as the previous two-report diagnostic."""
    out=Q(1)
    for t,received in enumerate(word,1):
        if t == 2 and word[0]=="got":
            out*=Q(1,2)
            continue
        equal=path[t][0]==path[t][1]
        miss=Q(3,4) if equal==(law=="plus") else Q(1,4)
        out*=miss if received=="miss" else 1-miss
    return out


def oracle(law,word,parity=None,local_x=None):
    """Independent exact trajectory enumeration and the physical loss sites."""
    mass=Q(0)
    loses={j:Q(0) for j in LOSS}
    d=Q(0)
    for path in product(STATES,repeat=5):
        eq=path[2][0]==path[2][1]
        if parity is not None and eq != parity:
            continue
        if local_x is not None and path[2][0] != local_x:
            continue
        m=Q(1,4)*path_likelihood(law,word,path)
        for s,t in zip(path,path[1:]):
            flips=sum(a!=b for a,b in zip(s,t))
            m*=FLIP**flips*(1-FLIP)**(2-flips)
        mass+=m
        d+=m*(1 if eq else -1)/4
        for tick,cell in LOSS.items():
            loses[tick]+=m*int(path[tick]==cell)
    assert mass
    return mass,d/mass,{j:p/mass for j,p in loses.items()}


def forward(law,word):
    p={s:Q(1,4) for s in STATES}
    for tick,received in enumerate(word,1):
        nxt={s:Q(0) for s in STATES}
        for s,t in product(STATES,repeat=2):
            r=Q(1,2) if tick==2 and word[0]=="got" else Q(3 if (t[0]==t[1])==(law=="plus") else 1,4)
            nxt[t]+=p[s]*local_transition(s[0],t[0])*local_transition(s[1],t[1])*(r if received=="miss" else 1-r)
        p=nxt
    return p


def actual_information(arrival, parity):
    # At t=2 the arrival phase precedes the irrevocable commitment phase;
    # t=3 receipt cannot retrospectively modify a selected dispatch reserve.
    issue_tick,decision=2,2
    if arrival is None:
        return (),None
    assert arrival >= issue_tick
    trace=((issue_tick,"measure_and_issue"),(arrival,"receive"),(decision,"commit"))
    return tuple(sorted(trace,key=lambda e:e[0])), parity if arrival<=decision else None


def minimax(rows):
    """Direct finite convex envelope of two affine conditional risks."""
    p0,p1 = rows
    delta0=p0[4]-p0[3]
    delta1=p1[4]-p1[3]
    candidates=[Q(0),Q(1)]
    if delta0!=delta1:
        r=(p1[3]-p0[3])/(delta0-delta1)
        if 0<=r<=1:
            candidates.append(r)
    return min(max(p0[3]+r*delta0,p1[3]+r*delta1) for r in candidates)


def noisy(cases,e):
    assert 0<=e<=Q(1,2)
    vals={}
    for word,laws in cases.items():
        for reading in (False,True):
            rows=[]
            for law in LAWS:
                r=laws[law]["parity"]
                m0,m1=r["False"]["mass"],r["True"]["mass"]
                n0=m0*(e if reading else 1-e)
                n1=m1*(1-e if reading else e)
                d=(n1-n0)/(4*(n0+n1))
                rows.append({3:Q(1,4)+LAM*d,4:Q(1,4)-LAM**2*d})
            vals[word,reading]=minimax(rows)
    return vals


def check():
    cases={}
    for word in WORDS:
        rows={}
        for law in LAWS:
            p=forward(law,word)
            z=sum(p.values())
            assert p[1,1]+p[1,0]==z/2 and p[1,1]+p[0,1]==z/2
            d=p[1,1]/z-Q(1,4)
            hazards={3:Q(1,4)+LAM*d,4:Q(1,4)-LAM**2*d}
            assert oracle(law,word)==(z,d,hazards)
            reveals={}
            for eq in (False,True):
                m,dt,hs=oracle(law,word,eq)
                assert dt==(Q(1,4) if eq else -Q(1,4))
                assert m==sum(p[s] for s in STATES if (s[0]==s[1])==eq)
                assert hs=={3:Q(1,4)+LAM*dt,4:Q(1,4)-LAM**2*dt}
                trace,available=actual_information(2,eq)
                assert trace[1][1]=="receive" and trace[2][1]=="commit"
                protect=3 if available else 4
                late,unavailable=actual_information(3,eq)
                assert unavailable is None and late[1][1]=="commit"
                assert actual_information(None,eq)[1] is None
                residual=hs[7-protect]
                assert residual<=Q(175,1024)<LIMIT
                reveals[str(eq)]=dict(mass=m, protect=protect, risk=residual)
            assert sum(r["mass"] for r in reveals.values())==z
            rows[law]=dict(mass=z,d=d,hazards=hazards,parity=reveals)
        assert rows["plus"]["mass"]==rows["minus"]["mass"]
        assert rows["plus"]["d"]==-rows["minus"]["d"]
        cases[word]=rows
    target=cases["miss","miss"]
    assert target["plus"]["mass"]==Q(73,256)
    assert target["plus"]["d"]==Q(25,146)
    for row in target.values():
        assert min(row["hazards"].values())<LIMIT
    r=1/(1+LAM)
    assert r==Q(16,25)
    assert minimax([row["hazards"] for row in target.values()])==Q(1,4)
    def risk(row,p):
        return p*row["hazards"][4]+(1-p)*row["hazards"][3]
    for rows in cases.values():
        assert all(risk(row,r)==Q(1,4) for row in rows.values())
        # Lines have equal midpoint, opposite slope. Their pointwise max
        # cannot fall below midpoint at any real p in [0,1].
        for n in range(26):
            vals=[risk(row,Q(n,25)) for row in rows.values()]
            assert sum(vals)==Q(1,2) and max(vals)>=Q(1,4)
    exante={law:sum(v[law]["mass"]*risk(v[law],r) for v in cases.values()) for law in LAWS}
    withinfo={law:sum(r["mass"]*r["risk"] for v in cases.values() for r in v[law]["parity"].values())
              for law in LAWS}
    assert exante==dict.fromkeys(LAWS,Q(1,4))
    assert withinfo==dict.fromkeys(LAWS,Q(287,2048))
    # A simpler accurate sensor of just X cannot deliver the same uniform
    # guarantee: on X=1 both laws give the same observation probability;
    # their average risk is > threshold whichever slot remains unprotected.
    local_rows=[oracle(law,("miss","miss"),local_x=1) for law in LAWS]
    assert local_rows[0][0]==local_rows[1][0]==Q(73,512)
    mean_local={j:sum(row[2][j] for row in local_rows)/2 for j in LOSS}
    assert mean_local=={3:Q(7,16),4:Q(25,64)} and min(mean_local.values())>LIMIT
    smallest=min((row["d"]*2+Q(1,2)) for rows in cases.values() for row in rows.values())
    assert smallest==Q(23,146)
    good_min=Q(661,810)
    bad_min=Q(61,90)
    e_positive=(smallest*(1-good_min))/(smallest*(1-good_min)+(1-smallest)*good_min)
    e_negative=(smallest*(1-bad_min))/(smallest*(1-bad_min)+(1-smallest)*bad_min)
    assert e_positive==Q(3427,84730)<e_negative
    last=noisy(cases,e_positive)
    assert max(last.values())==LIMIT and last[(("miss","miss"),True)]==LIMIT
    assert max(noisy(cases,e_positive+Q(1,10000)).values())>LIMIT
    return {"noisy_limit":e_positive, "risk_at_noisy_limit":max(last.values()),"words":{"-".join(k):v for k,v in cases.items()},"threshold":LIMIT,
            "minimax_protect_first":r,"coarse_minimax":Q(1,4),
            "parity_worst":Q(175,1024),"true_X_only_mean_hazard":mean_local,"ex_ante_coarse":exante,"ex_ante_parity":withinfo}


if __name__=="__main__":
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--json",action="store_true")
    v=check()
    print(json.dumps(v,default=str,indent=2,sort_keys=True) if cli.parse_args().json else
          {k: str(v[k]) for k in v if k!="words"})
