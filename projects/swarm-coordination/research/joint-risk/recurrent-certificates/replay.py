"""Exact recurrent risk certificates for a synthetic, civil loading facility."""
from collections import defaultdict
from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
import json

REPORT_MODES=("AB","A","","B")
STATES=tuple(product((0,1),repeat=2))
HORIZON=3
CAP=Q(1,2)
def chance(z):
    return Q(1+2*z,4)

def modes(law):
    return [(z,z if law=="aligned" else 1-z) for z in (0,1)]

def observations(regime):
    return tuple(product((0,1),repeat=len(regime)))

def local_report(bit,x):
    return Q(3 if bit==x else 1,4)

def policy(action,z):
    if action=="all": return True
    if action=="none": return False
    if action=="parity": return z[0]==z[1]
    raise ValueError(action)

@lru_cache(None)
def cert(z,obs):
    if obs is None:
        return Q(1),chance(z)
    p=chance(z)
    h=p*local_report(obs,1)
    return h+(1-p)*local_report(obs,0),h

def cert_filter(law,regimes,action):
    # Partition by executed policy's *public* resource decision, not by z.
    start=defaultdict(dict)
    for z in modes(law):
        start[(policy(action,z),())][z]=Q(1,2)
    reached={}
    stop={}
    for t,regime in enumerate(regimes):
        nxt=defaultdict(dict)
        for (protected,path),weights in start.items():
            for obs in observations(regime):
                read=dict(zip(regime,obs))
                key=(protected,path+(obs,))
                pred={}
                remain={}
                for z,w in weights.items():
                    a,af=cert(z[0],read.get("A"))
                    b,bf=cert(z[1],read.get("B"))
                    pred[z]=w*a*b
                    remain[z]=pred[z]-(0 if protected and t==1 else w*af*bf)
                reached[key]=(pred,remain)
                nxt[key]=remain
        start=nxt
    # Conditional risk of eventual loss after the current report and before this
    # dispatch, under this policy. Reports later than this cut are marginalized.
    for (protected,path),(pred,remain) in reached.items():
        t=len(path)-1
        later=len(regimes)-t-1-int(protected and t<1)
        stop[(protected,path)]=(sum(pred.values())-sum(
            w*(1-chance(z[0])*chance(z[1]))**later for z,w in remain.items()
            ))/sum(pred.values())
    return reached,stop

def independent(law,regimes,action):
    """Enumerate unnormalized physical branches, not local certificates."""
    cells={}
    losses=defaultdict(Q)
    done=Q(0)
    spent=Q(0)
    for za,zb in modes(law):
        z=(za,zb); protected=policy(action,z)
        spent+=Q(1,2)*protected
        def step(t,path,mass):
            nonlocal done
            if t==len(regimes): return
            mode=regimes[t]
            for x,y in STATES:
                local={"A":x,"B":y}
                p=mass*(chance(za) if x else 1-chance(za))*(chance(zb) if y else 1-chance(zb))
                failed=x==y==1 and not(protected and t==1)
                for obs in observations(mode):
                    q=p
                    for i,v in zip(mode,obs):
                        q*=local_report(v,local[i])
                    cur=path+(obs,)
                    key=protected,cur
                    pred,remain=cells.setdefault(key,(defaultdict(Q),defaultdict(Q)))
                    pred[z]+=q
                    if failed:
                        done+=q
                        # The loss belongs to each already reached risk cut.
                        for i in range(1,len(cur)+1):
                            losses[(protected,cur[:i])]+=q
                    else:
                        remain[z]+=q
                        step(t+1,cur,q)
        step(0,(),Q(1,2))
    return cells,{k:losses[k]/sum(pred.values()) for k,(pred,_) in cells.items()},done,spent

def coupled_censor():
    # In each mode, identical marginals under either censor kernel, but
    # dependence in the accepted event under the second. E is newly observed.
    out=[]
    for p,q in product((Q(1,4),Q(3,4)),repeat=2):
        u=[]
        for coupled in (False,True):
            table={
                (x,y):(p if x else 1-p)*(q if y else 1-q)*
                (Q(1,2)+(Q(1,2)*(x-p)*(y-q) if coupled else 0))
                for x,y in STATES}
            mass=sum(table.values())
            post={xy:v/mass for xy,v in table.items()}
            assert mass==Q(1,2)
            assert sum(v for (x,y),v in post.items() if x)==p
            assert sum(v for (x,y),v in post.items() if y)==q
            det=post[0,0]*post[1,1]-post[0,1]*post[1,0]
            assert det==(p*(1-p)*q*(1-q) if coupled else 0)
            # Adding the actual X bit makes each reached rectangle one row.
            split=Q(0)
            for x in (0,1):
                a=sum(post[x,y] for y in (0,1))
                if x:
                    split+=a*post[x,1]/a
            assert split==post[1,1]
            u.append(post[1,1])
        assert u[1]-u[0]==Q(9,256)
        out.append(dict(p=p,q=q,plain=u[0],dependent=u[1]))
    return out

def parity_regression():
    base={xy:Q(1,4) for xy in STATES}
    independent={(x,y,l):p/2 for (x,y),p in base.items() for l in (0,1)}
    selected={(x,y,l):(p if l==(x==y) else Q(0))
              for (x,y),p in base.items() for l in (0,1)}
    for coords in ((0,1),(0,2),(1,2)):
        for vals in STATES:
            assert sum(m for key,m in independent.items() if tuple(key[i] for i in coords)==vals)==Q(1,4)
            assert sum(m for key,m in selected.items() if tuple(key[i] for i in coords)==vals)==Q(1,4)
    losses=[p[1,1,1]/sum(m for key,m in p.items() if key[2]==1)
            for p in (independent,selected)]
    assert losses==[Q(1,4),Q(1,2)]
    return losses

def finite_signature_check():
    # Distinct latent modes may share the same admitted unprotected hazard.
    hazards=(Q(1,16),Q(9,16),Q(3,16),Q(3,16))
    budgets={}
    sigs={}
    weights=tuple(v for v in product(range(5),repeat=4) if sum(v)==4)
    for w in weights:
        by_h=tuple(sum(w[i] for i,r in enumerate(hazards) if r==h) for h in sorted(set(hazards)))
        tests=tuple(sum(Q(w[i],4)*(1-h)**k for i,h in enumerate(hazards)) for k in range(3))
        assert budgets.setdefault(by_h,tests)==tests
        assert sigs.setdefault(tests,by_h)==by_h
    return dict(weight_vectors=len(weights),distinct_signatures=len(sigs))

def serial(v):
    if isinstance(v,Q): return str(v)
    raise TypeError(v)

def main():
    scans=0
    main_cases={}
    for regime in product(REPORT_MODES,repeat=HORIZON):
        for law,action in product(("aligned","opposite"),("none","all","parity")):
            exact,qr=cert_filter(law,regime,action)
            oracle,oq,physical,cost=independent(law,regime,action)
            assert exact==oracle and qr==oq
            prediction=sum(sum(m.values()) for (a,h),(_,m) in exact.items()
                            if len(h)==HORIZON)
            assert 1-prediction==physical
            scans+=len(exact)
            if regime==("A","","B"):
                main_cases[law,action]={"mission_loss":physical,"reserve_cost":cost,
                    "max_reached_audit_suffix_risk":max(qr.values()),
                    "example":qr[policy(action,modes(law)[0]),((1,),(),(0,))]}
    assert main_cases["aligned","none"]["mission_loss"]==Q(2237,4096)>CAP
    assert main_cases["opposite","none"]["mission_loss"]==Q(1899,4096)<CAP
    assert main_cases["aligned","all"]["mission_loss"]==Q(119,256)<CAP
    assert main_cases["opposite","all"]["mission_loss"]==Q(87,256)<CAP
    assert main_cases["aligned","parity"]==main_cases["aligned","all"]
    assert main_cases["opposite","parity"]==main_cases["opposite","none"]
    rr,qr=cert_filter("aligned",("","",""),"none")
    survivors=rr[False,((),)][1]
    next_hazard=sum(w*chance(z[0])*chance(z[1]) for z,w in survivors.items())/sum(survivors.values())
    assert next_hazard==Q(39,176)!=Q(5,16)
    naive=1-(1-Q(1,4))**3
    redraw=1-(1-Q(5,16))**3
    assert CAP<main_cases["aligned","none"]["mission_loss"]<naive<redraw
    naive_protected=1-(1-Q(1,4))**2
    assert naive_protected<Q(9,20)<main_cases["aligned","all"]["mission_loss"]
    # Exact new conditional budget on a reached per-stage report/survival cut;
    # this explicitly does not claim a uniform 1/2 cap on every suffix of the
    # same ex-ante policy.
    result={"audited_report_cuts":scans,"regime_sequences":len(REPORT_MODES)**HORIZON,
      "coupled_censor":coupled_censor(),"v05_missing_report_regression":parity_regression(),
      "no_report_signature":finite_signature_check(),
      "mission":{"/".join(k):v for k,v in main_cases.items()},
      "naive_product_risk":naive,"naive_product_with_reserve":naive_protected,
      "redrawn_separator_risk":redraw,
      "conditional_second_hazard_after_success_no_reports":next_hazard,
      "minimum_unobserved_random_reserve_probability":Q(21,37)}
    print(json.dumps(result,default=serial,indent=2,sort_keys=True))

if __name__=="__main__":
    main()
