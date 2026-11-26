"""Native sampled effect windows, native observation provenance, exact join."""
from fractions import Fraction as Q
from hashlib import sha1
from itertools import product
from json import dumps, loads
from pathlib import Path
import random
import sys
from collections import Counter
from profile import Binding, compile_profile, runs

spaces, ptp_obs, prior, shared=map(Path,sys.argv[1:])
def pinned(p,h):
    b=p.read_bytes()
    assert sha1(f"blob {len(b)}\0".encode()+b).hexdigest()==h
pinned(prior/'calibration.py','d2a5c6355ec486c4e31065f5b5e315143881dd64')
pinned(shared/'core.py','687bf1250c6725992b6de696d0781d7948b4a89e')
sys.path[:0]=[str(prior),str(shared)]
from calibration import interval
from core import Event, Row, admitted

def direct(worlds,s,l,r):
    unknown=False
    for w in worlds:
        if w.resource is None:continue
        for t in range(s+l,s+r):
            j=t-w.shift
            if 0<=j<len(w.tape):
                if w.tape[j]:return 'conflict'
            else:
                unknown=True
    return 'unknown' if unknown else 'safe'

def native_cases():
    trace=loads(spaces.read_text())
    clock=[tuple(map(int,l.split())) for l in ptp_obs.read_text().splitlines()]
    assert len(trace)==10
    assert clock==[(6,1120,6,0),(6,1120,6,1),(9,1120,9,0),(9,1120,9,1)]
    return trace,clock

def aliases(w,spec):
    return tuple(Binding((j,i,d),i,d,tuple(z[i] for z in w['cells']))
                 for j,(i,d) in enumerate(spec))

def as_native(w,l,r,starts):
    # Adapter for the unchanged integration interpreter; no forecast is
    # inferred from a receipt. Options may use only observed modeled horizon.
    closed=[]
    for j,x in enumerate(w):
        bad=set()
        ready=set()
        if x.resource is not None:
            for i,b in enumerate(x.tape):
                tick=x.shift+i
                ready.add(('known',tick))
                if b:bad.add(('occupied',tick))
        opts={}
        for s in starts:
            ticks=range(s+l,s+r)
            required=frozenset(('known',t) for t in ticks) if x.resource is not None else frozenset()
            absent=frozenset(('occupied',t) for t in ticks)
            opts[s]=(Event(s,0,need=required,absent=absent,paid=('job',)),)
        closed.append(Row((),frozenset(ready|bad),(),opts))
    return admitted(closed,'crew',4,{'job':100},starts)[()]

def main():
    trace,native=native_cases()
    bank=next(x for x in trace if x['side']==0 and x['case']=='pre-conflict')
    l,r=0,2
    t=8
    opts=tuple(range(5,25))
    occ=[runs(tuple(z[i] for z in bank['cells'])) for i in range(2)]
    assert occ==[((7,17),(30,31)),((0,6),(19,32))]
    good=((0,3),(1,0))
    bad=((0,0),(1,3))
    loose=tuple(product(range(2),(0,3)))
    facts={}
    for tag,support in [('paired_safe',good),('paired_conflict',bad),('cartesian_without_binding',loose)]:
        worlds=aliases(bank,support)
        q=compile_profile(worlds,l,r)
        assert as_native(worlds,l,r,opts)==tuple(s for s in opts if q.verdict(s)=='safe')
        facts[tag]={'verdict_trim':q.verdict(t),'known':q.known_start,
                    'blocked':q.blocked,'at8_conflict_witnesses':[k for k,seg in q.support if seg[0]<=t<=seg[1]]}
    assert [x['verdict_trim'] for x in facts.values()]==['safe','conflict','conflict']

    # The native estimate/notification only qualifies the sample for this
    # authored acquisition interface. Error and offset bounds, timebase,
    # and latency are not measured by the inert LinuxPTP replay.
    def add(rows,source,received,raw,jitter,notice):
        assert native[(raw==9)*2+notice]==(raw,1120,raw,notice)
        if notice:rows.append((Q(source),Q(received),Q(raw-6-jitter),Q(raw-6+jitter)))
    cal={}
    for tag,older in [
        ('fresh_only',None),('valid_earlier_arrived',(-1,4,6,0,1)),
        ('same_poll_stale',(-1,4,6,0,0)),('valid_earlier_late',(-1,9,6,0,1)),
        ('valid_other_offset',(-1,4,9,0,1))]:
        samples=[]
        add(samples,2,4,6,3,1)
        if older:add(samples,*older)
        bound=interval(Q(0),Q(30),Q(4),samples,(Q(0),Q(3)),Q(1))
        assert bound is not None
        allowed=tuple(d for d in (0,3) if bound[0]<=d<=bound[1])
        # Exact direct acquisition check for this declared constant epoch
        # and a single prior sample within the admitted cut.
        direct_set=tuple(d for d in (0,3) if all(
            lo-max(0,-source,source-30)<=d<=hi+max(0,-source,source-30)
            for source,recv,lo,hi in samples if recv<=4))
        assert direct_set==allowed and allowed
        w=aliases(bank,[(1,d) for d in allowed])
        pr=compile_profile(w,l,r)
        assert as_native(w,l,r,opts)==tuple(z for z in opts if pr.verdict(z)=='safe')
        cal[tag]={'interval':list(map(str,bound)),'support':allowed,'verdict':pr.verdict(t)}
    assert [v['verdict'] for v in cal.values()]==['conflict','safe','conflict','conflict','conflict']
    departed=compile_profile(aliases(bank,[(1,0)]),l,r)
    assert departed.verdict(8)=='safe' and departed.verdict(18)=='conflict'
    assert departed.verdict(32)=='unknown'
    empty=compile_profile((Binding(('A',),0,0,()),),0,2)
    assert empty.verdict(3)=='unknown'
    disjoint=compile_profile((Binding(('B',),None,0,()),),0,2)
    assert disjoint.verdict(3)=='safe'
    # Different shape may invalidate a cached verdict even in one world.
    assert departed.verdict(17)=='safe'
    assert compile_profile(aliases(bank,[(1,0)]),0,3).verdict(17)=='conflict'
    mirror=next(x for x in trace if x['side']==1 and x['case']=='pre-conflict')
    left=tuple(z[0] for z in bank['cells'])
    right=tuple(z[1] for z in mirror['cells'])
    assert left==right
    cleared=Binding(('old-else',),0,3,left)
    one=Binding(('old-A',),0,0,left)
    other=Binding(('old-B',),1,0,right)
    lo1=(cleared,one)
    lo2=(cleared,one,other)
    p1,p2=(compile_profile(z,l,r) for z in (lo1,lo2))
    assert (p1.known_start,p1.blocked)==(p2.known_start,p2.blocked)
    assert p1.support!=p2.support
    amended=[compile_profile([q for q in z if q.key!=one.key],l,r).verdict(t)
             for z in (lo1,lo2)]
    assert amended==['safe','conflict']
    histogram=Counter()
    rng=random.Random(598)
    for _ in range(1200):
        w=[]
        for j in range(rng.randint(1,4)):
            site,d,plant=rng.choice((None,0,1)),rng.randint(-4,4),rng.choice(trace)
            tape=() if site is None else tuple(z[site] for z in plant['cells'][:rng.randint(0,len(plant['cells']))])
            w.append(Binding((j,),site,d,tape))
        a=rng.randint(-3,3);b=a+rng.randint(1,8)
        pr=compile_profile(w,a,b)
        for t0 in range(-10,41):
            verdict=pr.verdict(t0)
            assert verdict==direct(w,t0,a,b)
            histogram[verdict]+=1
    assert sum(histogram.values())==61200
    print(dumps(dict(warehouse_traces=len(trace),clock_raw_readings=native,
                     compiled_comparisons=dict(histogram),bay_occupancy=occ,
                     alias_support=facts,clock_conditioning=cal,
                     identical_profile_after_named_removal=amended),indent=2,sort_keys=True))
if __name__=='__main__':main()
