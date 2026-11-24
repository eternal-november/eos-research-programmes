#!/usr/bin/env python3
"""Forecast decisions with a byte-pinned inherited-work scheduler."""
import argparse
from fractions import Fraction as Q
from hashlib import sha256
from importlib.util import module_from_spec, spec_from_file_location
from itertools import combinations, product
import json
from pathlib import Path

SOURCE_HASH = "041224a331eca4f0c669ca88c57b62003041fab25671d59dfd91b1f9ed8ace33"
BASE = frozenset({'A2','B2','C2','D2','C3','D3'})
CELLS = ((1,1),(1,0),(0,1),(0,0))
HW = ((1,1),(0,1),(1,0),(0,0))
MENU = ('stay','prepare','divert')
PREP = {'new-tote': frozenset({'C2'})}
ALLOW = ('E3','C3')
MODES = ('early','late-F','late-F-atomic','late-W3','late-W4')
COSTS = (Q(0),Q(1,8),Q(3,8),Q(1,2))
DETOUR = (Q(1,2),Q(5,8),Q(3,4),Q(7,8),Q(1))
SOURCED = {}

def load_source(arg):
    here = Path(__file__).resolve().parent
    opts = [Path(arg)] if arg else [here / '../../role-changes/spare-slots/replay.py',
                                     here / '../swarm-c3-roles/replay.py', here / 'c3-source/replay.py']
    for p in opts:
        if p.is_file() and sha256(p.read_bytes()).hexdigest() == SOURCE_HASH:
            spec = spec_from_file_location('pinned_c3', p)
            mod = module_from_spec(spec)
            spec.loader.exec_module(mod)
            return mod
    raise SystemExit('Pass --source PATH to the exact #353 replay file; see README.')

def feasible(c3, pocket, action, detour_slot):
    old = c3.intersection([c3.edges_for(pocket, b) for b in (0,1)])
    extra = {'diversion-setup': frozenset({detour_slot})} if action == 'divert' else PREP if action == 'prepare' else {}
    slots = BASE | {'E3'}
    graph = old | extra
    key = (pocket, action, detour_slot)
    if key not in SOURCED:
        native = c3.matching(graph, slots)
        # Direct completely independent enumeration on new and still owed jobs.
        options = [tuple(graph[j] & slots) for j in sorted(graph)]
        direct = any(len(chosen) == len(set(chosen)) for chosen in product(*options))
        assert direct == (len(native) == len(graph))
        SOURCED[key] = native if direct else None
    return SOURCED[key]

def tape_sample():
    # W is drawn at tick 1 and H describes the later *baseline segment*.
    # B's health outcome is independent of both under each law.
    for f, (h,w), b in product((0,1), HW, (0,1)):
        yield (f,w,h,b)

def law_weight(tape, law):
    f,w,h,_ = tape
    i=HW.index((h,w))
    total=(3,1,1,3)[i]
    intact=((2,0,0,2) if law=='A' else (1,1,1,1))[i]
    return Q(intact if f else total-intact, 16)

def play(c3, tape, action, mode, detour_slot='E3'):
    f,w,h,b=tape
    pocket='intact' if f else 'damaged'
    plan=feasible(c3,pocket,action,detour_slot)
    assert plan is not None
    ready=feasible(c3,pocket,'prepare',detour_slot) is not None
    assert ready == bool(f)
    cert_tick = 3 if mode.startswith('late-F') else 2
    w_tick = 3 if mode == 'late-W3' else 4 if mode == 'late-W4' else 1
    tr = c3.timeline(pocket,b,BASE,{j:s for j,s in plan.items() if j!='diversion-setup'},action=='prepare')
    # The original "new-tote" uses C2 by the same current-gate authority.
    # In the intervention it is the shield installation, not a service receipt.
    tr = [[('shield-install' if x == 'new-tote' else x) for x in event] for event in tr]
    # C3 intake and execution telemetry belong to the separate old-work
    # dispatcher/gate. In particular, they are not mission observation fields.
    tr = [e+['gate-only'] if e[1]=='certified_intake_state' else e for e in tr]
    expected=[e for e in tr if e[1]=='physical_discharge' and e[2] in ('first-tote','second-tote')]
    assert [(e[0],e[2]) for e in expected] == [(2,'first-tote'),(3,'second-tote')]
    assert {e[0] for e in tr if e[1]=='coverage'} == {0,1,2,3}
    tr.append([w_tick,'mission-warning-received',w])
    tr.append([cert_tick,'mission-clearance-received', ready])
    if action=='prepare':
        assert plan['new-tote']=='C2' and ready
        assert (cert_tick <= 2) or mode == 'late-F-atomic'
        if mode == 'late-F-atomic':
            tr.append([2,'atomic-request-issued-and-granted','C2'])
        tr.append([3,'shield-effective','C2'])
    elif action=='divert':
        assert plan['diversion-setup']=='E3' and 'E3' not in BASE
        tr.append([3,'detour-switch-effective','E3'])
    # Fixed selector: the pre-route arrangement determines the traversed zone.
    # H is a potential exposure affecting the main zone, not a received detour outcome.
    zone = 'detour' if action=='divert' else 'main'
    shield = (action=='prepare')
    delay = False
    tr.append([4,'enter-zone',zone])
    if zone=='main':
        tr.append([5,'main-zone-disturbance-observed',h])
        if h and not shield:
            tr.append([5,'reactive-hold-safe'])
            delay=True
        elif h:
            tr.append([5,'shield-absorbs-interruption'])
    else:
        tr.append([5,'cross-independent-detour'])
    finish=6+int(delay)
    tr.append([finish,'recipient-served'])
    def order(event):
        tick, tag, *args = event
        # Gate installation/intake precede mission receipt, which precedes the
        # current operation commitment. Tick 3 receipts precede detour choice.
        phase = 0
        if tag in ('mission-clearance-received','mission-warning-received'):
            phase = 1
        elif tag == 'atomic-request-issued-and-granted':
            phase = 2
        elif 'shield-install' in args or tag in ('coverage','physical_discharge','detour-switch-effective'):
            phase = 3
        return (tick, phase)
    tr.sort(key=order)
    mission = tuple(tuple(e) for e in tr if e[1].startswith('mission-'))
    assert {e[1] for e in mission}=={'mission-warning-received','mission-clearance-received'}
    assert finish<=7 and set(plan.values()).issubset(BASE|{'E3'})
    assert len(set(plan.values()))==len(plan)
    return dict(trace=tr,mission_receipts=mission,slot_assignment=plan,delay=int(delay),finish=finish,
                cert_tick=cert_tick,w_tick=w_tick,zone=zone,clearance=ready)

def rule_set(c3, mode, detour_slot, menu=MENU):
    opts=[]
    for f,w in CELLS:
        pocket='intact' if f else 'damaged'
        opts.append([a for a in menu if feasible(c3,pocket,a,detour_slot) is not None and
                     not (mode=='late-F' and a=='prepare')])
    for tab in product(*opts):
        if mode in ('late-W3','late-W4'):
            # W arrives after the preparation cut. Each F uses one choice about
            # preparation across both Ws, though W3 can select the detour later.
            if any((tab[i]=='prepare') != (tab[i+1]=='prepare') for i in (0,2)):
                continue
        if mode=='late-W4' and any(tab[i]!=tab[i+1] for i in (0,2)):
            continue
        yield tab

def select(mode, tab, tape):
    f,w,_,_=tape
    j = CELLS.index((f,w))
    # These variables are those accessible at the named decisions, not raw tape.
    early_w = mode not in ('late-W3','late-W4')
    early_f = not mode.startswith('late-F')
    seen_f = f if early_f else None
    seen_w = w if early_w else None
    request = False
    if mode=='late-F-atomic':
        request = tab[CELLS.index((1,seen_w))] == 'prepare'
        grant = request and bool(f)  # different gate's already verified input
    elif seen_f:
        if seen_w is None:
            assert (tab[0]=='prepare') == (tab[1]=='prepare')
            grant = tab[0]=='prepare'
        else:
            grant = tab[CELLS.index((seen_f,seen_w))]=='prepare'
    else:
        grant = False
    if grant:
        called='prepare'
    elif mode=='late-W4':
        called=tab[CELLS.index((f,0))]
    else:
        # At tick 3 both W and the clearance record have arrived here.
        called=tab[j]
    assert called==tab[j] and (called=='prepare')==grant
    return called, request, grant

def risk_vectors(c3, mode, slot, c, d, traces, menu=MENU):
    out=[]
    for tab in rule_set(c3,mode,slot,menu):
        loss=[Q(0),Q(0)]
        for tape in tape_sample():
            act,_,_=select(mode,tab,tape)
            z=traces[(mode,slot,tape,act)]
            cost = z['delay'] + (c if act=='prepare' else d if act=='divert' else 0)
            for i,l in enumerate('AB'):
                loss[i] += law_weight(tape,l)*cost
        out.append((tab,tuple(loss)))
    return out

def optimize(rows):
    # Every randomized rule is a point in this finite convex hull. A minimum
    # occurs at a vertex or at a supporting segment crossing equality.
    opts = [(max(v), t, None, Q(1), v) for t,v in rows]
    for (t,u),(s,v) in combinations(rows,2):
        a,b=u[0]-u[1],v[0]-v[1]
        if a*b < 0:
            p=-b/(a-b)
            val = (p*u[0]+(1-p)*v[0],p*u[1]+(1-p)*v[1])
            assert val[0]==val[1]
            opts.append((val[0],t,s,p,val))
    minimum=min(z[0] for z in opts)
    # Prefer a deterministic attaining rule if there is one.
    return next(z for z in opts if z[0] == minimum)

def analyze(c3):
    traces={}
    for mode, slot, tape in product(MODES,ALLOW,tape_sample()):
        f,w,h,b=tape
        for a in MENU:
            if feasible(c3,'intact' if f else 'damaged',a,slot) is None or (mode=='late-F' and a=='prepare'):
                continue
            traces[(mode,slot,tape,a)]=play(c3,tape,a,mode,slot)
    for l in 'AB':
        assert sum(law_weight(t,l) for t in tape_sample())==1
    for i,j in combinations(range(3),2):
        for ab in product((0,1),repeat=2):
            assert sum(law_weight(t,'A') for t in tape_sample() if (t[i],t[j])==ab)==sum(law_weight(t,'B') for t in tape_sample() if (t[i],t[j])==ab)
    value={}
    for c,d in product(COSTS,DETOUR):
        v=lambda mode='early',slot='E3',menu=MENU: optimize(risk_vectors(c3,mode,slot,c,d,traces,menu))
        full=(1+c+min(c,d-Q(1,2)))/4
        no_prep=(Q(1,2)+2*min(Q(3,4),d))/4
        no_div=(1+2*c)/4
        assert v()[0]==v('late-F-atomic')[0]==full
        assert v('late-F')[0]==v(menu=('stay','divert'))[0]==no_prep
        assert v(slot='C3')[0]==v(menu=('stay','prepare'))[0]==no_div
        value[f'{c},{d}'] = dict(full=full, late_clearance=no_prep, detour_contended=no_div)
    center={}
    for mode in MODES:
        best=optimize(risk_vectors(c3,mode,'E3',Q(3,8),Q(3,4),traces))
        center[mode]=best
    assert [center[m][0] for m in MODES]==[Q(13,32),Q(16,32),Q(13,32),Q(14,32),Q(14,32)]
    # Cross same intact warning/hazard tape on all three routes, with late/atomic counterparts.
    t=(1,1,1,0)
    examples={f'{m}/{a}': traces[(m,'E3',t,a)] for m,a in
              [('early','stay'),('early','prepare'),('early','divert'),('late-F','stay'),('late-F-atomic','prepare')]}
    # Explicit reached denial invokes the atomically addressed gate, not the
    # controller's hidden knowledge of the pocket. The late receipt still lets
    # the same warning trigger the independent detour.
    td=(0,1,1,0)
    action, request, grant=select('late-F-atomic',center['late-F-atomic'][1],td)
    assert request and not grant and action=='divert'
    denied=dict(traces[('late-F-atomic','E3',td,action)])
    denied['trace']=sorted(denied['trace']+[[2,'atomic-request-issued-and-denied','C2']], key=lambda e:e[0])
    examples['late-F-atomic/damaged-request']=denied
    for b in (False,True):
        assert c3.direct(c3.edges_for('damaged',b),PREP,BASE) == b
    final_scope={'source_profile_checks':len(SOURCED),'common_tapes':len(tuple(tape_sample())),
                 'route_interventions':len(traces),'cost_grid_points':len(value)}
    return dict(scope=final_scope,phase_grid=value,center_policy=center,example_traces=examples)

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source')
    parser.add_argument('--verify',action='store_true')
    a=parser.parse_args()
    result=json.dumps(analyze(load_source(a.source)),indent=2,sort_keys=True,default=str)+'\n'
    if a.verify:
        assert result==Path(__file__).with_name('results.json').read_text()
    print(result,end='')
