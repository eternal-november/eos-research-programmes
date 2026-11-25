"""One receiving rule; two distinct typed civil source laws."""
from dataclasses import dataclass
from itertools import product
from collections import defaultdict

@dataclass(frozen=True)
class World:
    second: str  # A/B local projection, Common disables a shared dependency
    old_duty: bool
    delivery_lag: int = 0
    pack_end: int = 5
    second_cut: int = 2  # public latest scheduled injection boundary in this laboratory family

@dataclass(frozen=True)
class Interface:
    # A typed effect-ready window, not an answer about the joint mission.
    handle: str
    time: int
    witness_kind: str
    ready_since: int
    valid_until: int

def selection(windows,options,cut,old_expires,latest):
    # Equal cuts, declared duration 2, old effect through acquisition, and an
    # actual consequence before the mission-derived last-effect cutoff.
    valid={item.handle for item in windows
           if item.handle in options and item.time<=cut and item.ready_since<=cut
           and cut+2<=min(item.valid_until,old_expires,latest)}
    return min(valid) if valid else None

def diagnosis(installed,cut,kind):
    # Setup is an admitted physical event occupying the single independent
    # diagnostic slot during [1,2); it cannot produce new facts before that.
    # Same setup is charged to every matched comparison using this channel.
    if not installed or cut<2:return ()
    return ((1,'reserve-' + kind + '-diagnostic-slot'),(2,'arm-' + kind))

class Custody:
    last_effect_cut=6 # the report can be read at the deadline
    @staticmethod
    def plant(w,cut,old_duty=None):
        # Photointerruptor detects insertion of the durable recorder into
        # either physical dock. The earlier data are held in recorder P.
        # Sector-wide wiring loss disables the recording head both docks share.
        r={(k):(cut<w.second_cut or w.second!=k) for k in ('A','B')}
        good_head=cut<w.second_cut or w.second!='Common'
        return {k:r[k] and good_head for k in r}
    @staticmethod
    def report(w,installed,cut):
        if not diagnosis(installed,cut,'optical') or cut<3+w.delivery_lag or w.second_cut<=cut<w.second_cut+1+w.delivery_lag:return ('unknown',(),cut)
        return ('dock',tuple(k for k,z in Custody.plant(w,cut).items() if z),
                w.second_cut if cut<w.second_cut else 6)
    @staticmethod
    def execute(w,choice,cut,stop=False):
        # Such events share a source timeline. The sole physical holder
        # changes on both actual writes plus observed latch, not on issue.
        events=[(0,'rf-down'),(w.second_cut,'dock-loss:'+w.second)]
        holder='P'
        if stop:
            assert cut+1<=w.pack_end
            events.append((cut+1,'sealed-old-at-local-safe-depot'))
            return True,0,events
        for t in range(6):
            if t>=w.pack_end and holder=='P':
                return False,0,events
            if t==cut:
                events.append((t,'write-start:'+choice))
            if cut<=t<cut+2:
                if not Custody.plant(w,t)[choice]:
                    return False,0,events
                events.append((t,'write-tick:'+choice))
            if t+1==cut+2:
                holder=choice
                events.append((t+1,'verified-custody:'+holder))
        events.append((6,'read-report:'+holder))
        return True,int(holder!='P'),events

class Cooling:
    last_effect_cut=5 # at least one physical tick from the replacement before 6
    @staticmethod
    def plant(w,cut):
        # Distinct realization: consumption of power requires two real units
        # at once. Both auxiliary routes draw from the same base bus.
        return (int(cut<w.second_cut or w.second!='Common'),
                {k:int(cut<w.second_cut or w.second!=k) for k in ('A','B')})
    @staticmethod
    def report(w,installed,cut):
        if diagnosis(installed,cut,'current-meter') and cut>=3+w.delivery_lag and not (w.second_cut<=cut<w.second_cut+1+w.delivery_lag):
            base,aux=Cooling.plant(w,cut)
            return ('current',(base,aux['A'],aux['B']),w.second_cut if cut<w.second_cut else 6)
        return ('unknown',(),cut)
    @staticmethod
    def execute(w,choice,cut,stop=False):
        events=[(0,'feeder-down'),(w.second_cut,'supply-loss:'+w.second)]
        if stop:
            assert cut+1<=w.pack_end
            events.append((cut+1,'protected-load-shutdown'))
            return True,0,events
        energized=False
        for t in range(6):
            if t==cut:
                events.append((t,'energize-standby:'+choice))
            base,aux=Cooling.plant(w,t)
            if cut<=t<cut+2 and base+aux[choice]<2:
                return False,0,events
            if t==cut+2:
                energized=True
                events.append((t,'flow-established:'+choice))
            power=base+aux[choice] if energized else 2*int(t<w.pack_end)
            events.append((t,'delivered-units:'+str(power)))
            if power<2:
                return False,0,events
        events.append((6,'required-cooling-delivered'))
        return True,int(energized),events

def scoped_option(report,cut):
    # Bound the new controls by evidence, actual allowed timing and declared
    # shared-dependency rule. It does not consume an oracle for the joint goal.
    kind,x,end=report
    if kind=='unknown':return ()
    if kind=='dock':
        legal=x
    elif kind=='current':
        b,p,q=x
        legal=tuple(k for k,a in zip(('A','B'),(p,q)) if a+b>=2)
    else:
        raise ValueError(kind)
    return tuple(Interface(k,cut,kind,cut,end) for k in legal)

def fixture(plant, worlds, cut, install=True, common_allowed=False):
    observed=defaultdict(list)
    for w in worlds:
        obs=plant.report(w,install,cut)
        # External deadline cap at the primary holder is a shared pin. A
        # successor adapter must supply it rather than obtaining it here from w.
        observed[obs].append(w)
    assert len({w.pack_end for w in worlds})==1
    e=worlds[0].pack_end
    optional=0
    for view,cell in observed.items():
        rows=scoped_option(view,cut)
        k=selection(rows,('A','B'),cut,e,plant.last_effect_cut)
        if k is None and cut+1>e:
            return False,0,{}
        out=[plant.execute(w,k,cut,k is None) for w in cell]
        if not all(x[0] for x in out):return False,0,{}
        if k is not None: assert all(x[1]==1 for x in out)
        if k is None and not common_allowed:return False,0,{}
        optional+=sum(x[1] for x in out)
    return True,optional,observed

def direct(plant,worlds,cut,install,allow_stop=False):
    # Independent direct scenario-response enumeration matches local
    # observation and actual effect prerequisites, never gives ground truth.
    reports=tuple(sorted({plant.report(w,install,cut) for w in worlds}))
    highest=-1
    for choices in product(('A','B',None) if allow_stop else ('A','B'),repeat=len(reports)):
        policy=dict(zip(reports,choices));value=0
        for w in worlds:
            act=policy[plant.report(w,install,cut)]
            if act is None and cut+1>w.pack_end: break
            ok,j,events=plant.execute(w,act,cut,act is None)
            # A new effect cannot continue if reliable authority/evidence
            # is missing even if that action was physically available.
            obs=plant.report(w,install,cut)
            if act is not None and (obs[0]=='unknown' or cut+2>obs[2]):break
            if not ok or (not allow_stop and not j):break
            value+=j
        else:
            highest=max(highest,value)
    return highest>=0, max(0,highest)

def current_occupancy(plant,w,scope,effect_receipt):
    # Every source offers same restart verb, but each reports actual old work
    # via a different local supplier before the optional operation's start.
    if plant==Custody:
        physical='old recorder still latched' if w.old_duty else 'old recorder drained'
    else:
        physical='old capacitor still discharging' if w.old_duty else 'old capacitor drained'
    return (scope,not w.old_duty,physical) if effect_receipt else (scope,False,'last restart status')

def response(verify):
    # Scope-specific actual positive clearance, never infer absence of use
    # from restart. Shared codes are valid physical inputs to this check.
    scope,clear,source=verify
    return scope=="restart-old-right" and clear and source in ("old recorder drained","old capacitor drained")

def replay_scope(P,w,install,unsafe_status_policy=False):
    # Effect-side gate cannot infer clearance from the restarted process.
    # Its supplier either reads the old carrier's physical latch, or checks
    # the old discharge register, at the same cut and for the same use.
    events=[(0,'restart status: idle')]
    if install:events.append((1,'paid local inspection'))
    physical=current_occupancy(P,w,'restart-old-right',install)
    if unsafe_status_policy or response(physical):
        events.append((1,'attempt optional slot'))
        if w.old_duty:
            return False,False,events
        events.append((2,'optional slot executed and settled'))
        return True,True,events
    return True,False,events

def paired_effect_controls():
    for P in (Custody,Cooling):
        for mode,old,probe in product(('A','B'),(False,True),(False,True)):
            w=World(mode,old)
            ok,extra,extra_trace=replay_scope(P,w,probe)
            safety,performed,trace=P.execute(w,'B' if mode=='A' else 'A',3)
            assert ok and safety and performed==1 and extra==(probe and not old)
            assert all(t<=6 for t,_ in sorted(extra_trace+trace))
            unsafe=not replay_scope(P,w,False,True)[0]
            assert unsafe==old
        # The common cause is strongest in the feeder: both auxiliaries
        # independently advertise 1, but the exclusive selector can't draw
        # both, and no base power is present. Local guarantees survive.
        w=World('Common',True)
        if P==Cooling:
            base,aux=P.plant(w,3)
            assert base==0 and all(v==1 for v in aux.values())
        assert selection(scoped_option(P.report(w,True,3),3),('A','B'),3,5,P.last_effect_cut) is None
        assert P.execute(w,None,3,True)[:2]==(True,0)
    print('16 paired old-authority traces; matched restart status, physically different optional admission')

def main():
    for P in (Custody,Cooling):
        kind='optical' if P is Custody else 'current-meter'
        assert diagnosis(True,1,kind)==()
        assert diagnosis(True,3,kind)==((1,'reserve-'+kind+'-diagnostic-slot'),(2,'arm-'+kind))
        assert not diagnosis(False,6,kind)
        cases=(World('A',False),World('A',True),World('B',False),World('B',True))
        full=fixture(P,cases,3)
        assert full[0] and full[1]==4
        assert not fixture(P,cases,3,False)[0]
        assert not fixture(P,tuple(World(w.second,w.old_duty,1) for w in cases),3)[0]
        common=cases+(World('Common',True),)
        contained=fixture(P,common,3,True,True)
        assert contained[0] and contained[1]==4 # common failure protected, one missed.
        for o in (False,True):
            w=World('A',o)
            assert not response(current_occupancy(P,w,'restart-old-right',False))
            assert response(current_occupancy(P,w,'restart-old-right',True))==(not o)
            assert not response(current_occupancy(P,w,'different right',True))
    trials=0
    for P,lag,end,t,install,common,soft,phase in product(
        (Custody,Cooling),range(3),range(4,8),range(3,5),(True,False),(False,True),(False,True),(2,4)):
        ws=tuple(World(s,o,lag,end,phase) for s in ('A','B','Common')[:3 if common else 2] for o in (False,True))
        a=fixture(P,ws,t,install,soft)[:2]
        b=direct(P,ws,t,install,soft)
        assert a==b,(P.__name__,lag,end,t,install,common,soft,a,b)
        trials+=1
    for P in (Custody,Cooling):
        worlds=(World('A',False,0,5,4),World('B',True,0,5,4))
        reports=[P.report(w,True,3) for w in worlds]
        assert reports[0]==reports[1] and reports[0][2]==4
        assert not fixture(P,worlds,3)[0]
        assert fixture(P,worlds,3,True,True)[:2]==(True,0)
        # Stale readiness appears favorable if expiry is read as just status.
        stale=reports[0][:2]+(6,)
        k=selection(scoped_option(stale,3),('A','B'),3,5,P.last_effect_cut)
        assert k and not all(P.execute(w,k,3)[0] for w in worlds)
    print('a later loss during acquisition is caught by the certified horizon; the status-only ablation is unsafe')
    print(trials,'matched same-information cases: custody holder and shared additive load')
    print('positive service through two faults and lost RF; common shared failure is containment only')
    paired_effect_controls()
    print('restart status cannot certify optional early entry when old authority is live')
if __name__=='__main__':main()
