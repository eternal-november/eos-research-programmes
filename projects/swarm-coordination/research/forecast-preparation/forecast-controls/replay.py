"""Exact decision tables for an extension of the pinned C7 maintenance plant."""
from fractions import Fraction as Q
from functools import lru_cache
from hashlib import sha256
from itertools import product
from pathlib import Path
import json
import original as old

ROOT=Path(__file__).resolve().parent
PIN="f142e0d8d4f9813508ba33494b37e55e62dc8d61b1c0941c151ba44530d17443"
assert sha256((ROOT/'original.py').read_bytes()).hexdigest()==PIN
C3=old.load_source(ROOT/'c3-source/replay.py')
INF=99

def scenarios(plus,minus):
    """One common tape includes the independent warning-channel draw."""
    for t,m in product(old.tape_sample(),(0,1)):
        f,w,h,b=t
        p=minus if w else plus
        yield (t,w^m),(old.law_weight(t,'A')*(p if m else 1-p),
                         old.law_weight(t,'B')*(p if m else 1-p))

def recipient(t):
    return t if t in (1,2,3,4) else INF

def prep_key(t,v,mt,gt,owner):
    f,w,h,b=t
    at=mt if owner=='mission' else gt
    return f,v if at<=2 else None

def final_key(t,v,p,mt,confirm):
    f,w,h,b=t
    # Gate warning is not relayed. Confirm is an independent *advance*
    # measurement of the main zone potential, not a realized route outcome.
    return f,v if mt<=3 else None,p,h if confirm else None

def options(p,rev,slot):
    if p:
        return ('keep','release','release-divert') if rev and slot=='E3' else ('keep','release') if rev else ('keep',)
    return ('stay','divert') if slot=='E3' else ('stay',)

def outcome(h,p,a,c,d,g,r):
    sunk=c if p else Q(0)
    if a=='keep': return sunk+g
    if a=='release': return sunk+r+h
    if a=='release-divert': return sunk+r+d
    if a=='stay': return Q(h)
    if a=='divert': return d
    raise AssertionError(a)

@lru_cache(None)
def plant(t,p,a,slot):
    f,w,h,b=t
    route0='prepare' if p else 'divert' if a=='divert' else 'stay'
    z=old.play(C3,t,route0,'early',slot)
    # The original replay supplies all inherited admissions, closure,
    # relay, shielding and capacity events. Replace the *future* route episode.
    tr=[e for e in z['trace'] if e[0]<4 and not e[1].startswith('mission-')]
    to_detour=a in ('divert','release-divert')
    if a.startswith('release'):
        assert p and f
        tr.append([3,'withdraw-reversible-shield'])
    if a=='release-divert':
        assert z['slot_assignment']['new-tote']=='C2' and slot=='E3'
        extra=old.feasible(C3,'intact', 'divert',slot)
        assert extra['diversion-setup']=='E3' and 'E3' not in z['slot_assignment'].values()
        tr.append([3,'detour-switch-effective','E3'])
    armed=p and a=='keep'
    zone='detour' if to_detour else 'main'
    tr.append([4,'enter-zone',zone])
    delay=int(zone=='main' and h and not armed)
    if zone=='detour': tr.append([5,'cross-independent-detour'])
    else:
        tr.append([5,'main-zone-disturbance-observed',h])
        if h: tr.append([5,'shield-absorbs-interruption' if armed else 'reactive-hold-safe'])
    tr.append([6+delay,'recipient-served'])
    assert [(e[0],e[2]) for e in tr if e[1]=='physical_discharge' and e[2] in ('first-tote','second-tote')]==[(2,'first-tote'),(3,'second-tote')]
    assert {e[0] for e in tr if e[1]=='coverage'}=={0,1,2,3}
    return tr,delay

def observed_trace(t,v,p,a,mt,gt,owner,confirm):
    tr=list(plant(t,p,a,'E3')[0])
    tr.extend([[t0,'warning-received',who,v] for t0,who in
               [(mt,'mission'),(gt,'gate')] if t0<INF])
    tr.append([2,'clearance-received','mission',bool(t[0])])
    tr.append([2,'preparation-controller',owner])
    tr.append([3,'shield-status-received',bool(p)])
    if confirm: tr.append([3,'advance-main-zone-confirmation',t[2]])
    def phase(e):
        tag=e[1]
        if tag in ('warning-received','clearance-received','shield-status-received',
                   'advance-main-zone-confirmation'): return 1
        if tag=='preparation-controller': return 2
        if 'shield-install' in e or tag in ('withdraw-reversible-shield','detour-switch-effective',
                                            'physical_discharge','coverage'): return 3
        return 0
    return sorted(tr,key=lambda e:(e[0],phase(e)))


def family(mt,gt,owner,confirm,rev,slot,c,d,g,r,plus,minus):
    cases=tuple(scenarios(plus,minus))
    k2=sorted({prep_key(t,v,mt,gt,owner) for (t,v),weights in cases
               if any(weights)},key=repr)
    rows=[]
    for bits in product(*[range(2) if f else (0,) for f,_ in k2]):
        tab2=dict(zip(k2,bits))
        choices=[(t,v,weights,tab2[prep_key(t,v,mt,gt,owner)])
                 for (t,v),weights in cases if any(weights)]
        k3=sorted({final_key(t,v,p,mt,confirm) for t,v,_,p in choices},key=repr)
        def acts(k):
            opts=options(k[2],rev,slot)
            # With a truthful separate confirmation, each action has a
            # common deterministic cost on this cell, hence pointwise dominance
            # simultaneously for both admitted laws.
            if confirm:
                return (min(opts,key=lambda a:outcome(k[3],k[2],a,c,d,g,r)),)
            return opts
        for codes in product(*map(acts,k3)):
            tab3=dict(zip(k3,codes)); sums=[Q(0),Q(0)]
            for t,v,mass,p in choices:
                a=tab3[final_key(t,v,p,mt,confirm)]
                _,delta=plant(t,p,a,slot)
                val=outcome(t[2],p,a,c,d,g,r)
                assert val==delta+(c if p else 0)+(g if a=='keep' else 0)+(r if a.startswith('release') else 0)+(d if a.endswith('divert') else 0)
                for i in (0,1): sums[i]+=mass[i]*val
            rows.append(((bits,codes),tuple(sums)))
    optimal=old.optimize(rows)
    # Dual certificate: for lambda mixing A and B, the worst risk is >=
    # lower envelope of affine risks in lambda; vertices of that piecewise
    # linear graph suffice. Independent of the primal two-policy formula.
    vertices={Q(0),Q(1)}
    vals={v for _,v in rows}
    for a,b in vals:
        for u,v in vals:
            denom=(a-b)-(u-v)
            if denom:
                k=(v-b)/denom
                if 0<=k<=1: vertices.add(k)
    dual=max((min(k*a+(1-k)*b for a,b in vals),k) for k in vertices)
    assert dual[0]==optimal[0]
    return optimal, len(rows), dual[1]

def fixed(mt,gt,owner,slot,c,d,g,r,plus,minus):
    vals={k:[Q(0),Q(0)] for k in ('reactive','always-clear','forecast-prep','forecast-avoid','always-avoid')}
    for (t,v),mass in scenarios(plus,minus):
        if not any(mass): continue
        f=t[0]; _,early=prep_key(t,v,mt,gt,owner)
        for k in vals:
            p=f and (k=='always-clear' or (k=='forecast-prep' and early==1))
            a='keep' if p else 'divert' if slot=='E3' and (k=='always-avoid' or (k=='forecast-avoid' and mt<=3 and v)) else 'stay'
            _,delta=plant(t,p,a,slot)
            assert outcome(t[2],p,a,c,d,g,r)==delta+(c+g if p else 0)+(d if a=='divert' else 0)
            for i in (0,1): vals[k][i]+=mass[i]*outcome(t[2],p,a,c,d,g,r)
    return {k:max(v) for k,v in vals.items()}

def rates(plus,minus,l):
    i='AB'.index(l)
    return tuple(sum(m[i] for (t,v),m in scenarios(plus,minus) if t[2]==h and v==1-h) /
                 sum(m[i] for (t,v),m in scenarios(plus,minus) if t[2]==h) for h in (1,0))

def main():
    def run(mt,gt,owner='mission',confirm=False,rev=False,slot='E3',
            c=Q(3,8),d=Q(3,4),g=Q(0),r=Q(0),fp=Q(0),fn=Q(0)):
        args=(recipient(mt),recipient(gt),owner,slot,c,d,g,r,fp,fn)
        best,nb,lam=family(*args[:3],confirm,rev,*args[3:])
        return {'best':best[0],'attaining_policy':best[1:], 'rules':nb,'dual_Law_A':lam,
                'fixed':fixed(*args),'miss_false_by_law':[rates(fp,fn,l) for l in 'AB']}
    center={'early-mission':run(1,INF),'on-decision':run(2,INF),'late':run(3,INF),
            'too-late':run(4,INF),'nobody':run(INF,INF),'gate-withstanding':run(INF,1,'gate'),
            'gate-without-standing':run(INF,1),'both':run(1,1,'gate'),
            'inherited-detour-conflict':run(1,INF,slot='C3')}
    assert center['early-mission']['best']==Q(13,32)
    assert center['on-decision']['best']==center['early-mission']['best']
    assert center['late']['best']==center['too-late']['best']==Q(14,32)
    assert center['nobody']['best']==center['gate-without-standing']['best']
    assert center['both']['best']==center['early-mission']['best']
    assert tuple(center['early-mission']['fixed'].values())==(Q(1,2),Q(7,16),Q(15,32),Q(1,2),Q(3,4))
    error_cost={str((fp,fn,c)):run(1,INF,c=c,fp=fp,fn=fn)
                for fp,fn,c in product((Q(0),Q(1,4),Q(1,2)),(Q(0),Q(1,4),Q(1,2)),(Q(1,8),Q(3,8)))}
    reversible={config:run(1,INF,confirm=True,rev=rev,c=Q(1,8),d=Q(3,4),g=Q(1,4),r=r)
                for config,rev,r in [('lock',False,Q(1,16)),('reopen',True,Q(1,16)),('reopen-high-fee',True,Q(1,4))]}
    assert reversible['reopen']['best']<reversible['lock']['best']==reversible['reopen-high-fee']['best']
    reverse_boundary={}
    for fee in (Q(0),Q(1,16),Q(1,8),Q(3,16),Q(1,4),Q(1,2)):
        cost=run(1,INF,confirm=True,rev=True,c=Q(1,8),d=Q(3,4),g=Q(1,4),r=fee)['best']
        assert cost == Q(5,16)+min(fee,Q(1,4))/4
        reverse_boundary[str(fee)]=cost
    same=(1,1,0,0)
    example={a:observed_trace(same,1,True,a,1,INF,'mission',True)
             for a in ('keep','release','release-divert')}
    example['gate-only-forecast-prep']=observed_trace(same,1,True,'keep',INF,1,'gate',False)
    example['late-mission-forecast-avoid']=observed_trace(same,1,False,'divert',3,INF,'mission',False)
    print(json.dumps(dict(center=center,error_cost=error_cost,reversible=reversible,
                          reversal_fee_boundary=reverse_boundary,example_traces=example,
                          distinct_plant_routes=plant.cache_info().currsize),default=str,sort_keys=True,indent=1))

if __name__=='__main__': main()
