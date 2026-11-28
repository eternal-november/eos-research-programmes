"""Fixed schedule transport across two named, physically bound gate crossings."""
from pathlib import Path
from fractions import Fraction as Q
from itertools import pairwise, product
from math import isqrt
import ast, json, sys
P=Path(sys.argv[1])
S=10**6
dwell=200000
pad=Q(302,1000)
def floor(v):return v.numerator//v.denominator
def ceil(v):return -floor(-v)
def windows(p,slab):
    t=S; out=[]
    for a,b in pairwise(p):
        lo,hi=Q(0),Q(1)
        n=sum((i-j)**2 for i,j in zip(a,b))
        k=isqrt(n*S*S)
        assert k>=200000
        K=k+(k*k!=n*S*S)
        for x,y,L,H in zip(a,b,*slab):
            B=L-pad; T=H+pad
            if x==y:
                if not B<=x<=T:
                    lo,hi=Q(1),Q(0)
                    break
            else:
                l,h=sorted(((B-x)/(y-x),(T-x)/(y-x)))
                lo,hi=max(lo,l),min(hi,h)
        if lo<=hi:
            # Actual padded occupancy boundaries fall in the cruise phase.
            # At unit speed the phase time is distance plus the 0.1 s
            # ramp correction; bracket Euclidean length in integer microns.
            assert lo*k>100000 and (1-hi)*k>100000
            out.append(((t+100000+floor(lo*k),t+100000+ceil(lo*K)),
                        (t+100000+floor(hi*k),t+100000+ceil(hi*K))))
        t+=K+dwell
    return out,t

def parse_slabs():
    tree=ast.parse((P/'ride.py').read_text())
    for a in tree.body:
        if isinstance(a,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='closures' for t in a.targets):
            # Never execute source to decode this fixed boundary datum:
            # demand Decimal literal calls of the exact pinned format.
            obj=a.value;assert isinstance(obj,ast.Dict)
            def interval(e):
                assert isinstance(e,ast.Tuple)
                row=[]
                for arg in e.elts:
                    assert isinstance(arg,ast.Call) and isinstance(arg.func,ast.Name) and arg.func.id=='D'
                    assert len(arg.args)==1 and not arg.keywords
                    value=ast.literal_eval(arg.args[0]);assert isinstance(value,str)
                    row.append(Q(value))
                assert len(row)==3
                return tuple(row)
            return {ast.literal_eval(key):tuple(interval(e) for e in v.elts)
                    for key,v in zip(obj.keys,obj.values)}
    raise AssertionError("no pinned slabs")
paths=json.loads((P/'paths.json').read_text())
binding=json.loads((P/'EXPECTED.jsonl').read_text().splitlines()[0])
assert binding["route_requiring_gate"]==[0,1]
slabs=parse_slabs()
assert set(slabs)=={(118,132),(117,132)}
gates=[slabs[117,132],slabs[118,132]]
routes=[paths[x]['polyline'] for x in "AB"]
def intersects(a,b):return max(a[0],b[0])<=min(a[1],b[1])
def contained(a,b):return b[0]<=a[0]<=a[1]<=b[1]
def generate(k):
    gate=gates[k];p=routes[k]
    hits,end=windows(p+p[-2::-1],gate)
    no,_=windows(p+p[-2::-1],gates[1-k])
    assert len(hits)==2 and not no
    egress=max(v['max_egress_us'] for v in json.loads((P/'EXPECTED.jsonl').read_text().splitlines()[1]).values())
    assert end<egress<454*S
    # No prerelease radio reboot or repair wait may precede the inbound
    # crossing. A proof concerning a retimed schedule must recheck this.
    hulls=[(enter[0],leave[1]) for enter,leave in hits]
    cores=[(enter[1],leave[0]) for enter,leave in hits]
    assert all(b-a>500000 for a,b in cores)
    o,i=hulls
    assert i[1]<end
    reqs={"out":cores[0],"in":cores[1],
          "maintenance":(o[1]+S,o[1]+101*S),
          "idle":None,"edge_before":(o[0]-S,o[0]-1),
          "edge_after":(i[1]+1,i[1]+S)}
    assert reqs['maintenance'][1]<i[0] and reqs['edge_after'][1]<end
    return dict(hulls=hulls,cores=cores,end=end,requests=reqs)

def evaluate(z):
    windows=z["hulls"]
    envelope=(windows[0][0],windows[1][1])
    core=z["cores"]
    raw=[]
    modes=("snapshot","envelope","first","split","volatile_split")
    for name, mode, change in product(z['requests'],modes,(False,True)):
        request=z['requests'][name]
        holds={"snapshot":(),"envelope":(envelope,),"first":(windows[0],),
               "split":tuple(windows),
               "volatile_split":tuple(windows[:1] if change else windows)}[mode]
        # Ownership change is after the first padded contact and before
        # all offered return-side effects. No spontaneous obstacle drift.
        enabled=bool(request) and not any(intersects(h,request) for h in holds)
        actual=request if enabled else None
        contact=tuple(bool(actual and intersects(w,actual)) for w in windows)
        assert all(not hit or intersects(w,actual) for w,hit in zip(core,contact))
        maintenance=(enabled if name=="maintenance" else False)
        raw.append(dict(case=(name,mode,change),receipt=("OPEN",0),effect=actual,
                        contact=contact,air=maintenance))
    def tests(row):
        return (*row['contact'],row['air'],row['receipt'])
    classes={tests(x) for x in raw}
    # Exhaust the fixed source -> OPEN snapshot projection obstructions.
    witness=lambda x: x['case'] in [('idle','split',False),('in','snapshot',True)]
    xx=[x for x in raw if witness(x)]
    assert len(xx)==2 and xx[0]['receipt']==xx[1]['receipt'] and tests(xx[0])!=tests(xx[1])
    # Reflection T and attained residual-class coverage C at the proposed
    # comparison, for precisely these declared effect/service consumers.
    # The enriched interface evaluates from actual gate-effect intervals,
    # not from mode names or from the answer to a downstream task.
    # Service input comes from independently named maintenance metadata and
    # presence of the matching effect, not the route admission output.
    def take(row):
        return row['effect'],row['case'][0]=="maintenance",row['receipt']
    def decode(export):
        eff,named,rec=export
        return (*tuple(bool(eff and intersects(w,eff)) for w in windows),bool(eff and named),rec)
    both={take(x) for x in raw}
    assert all(decode(take(r))==tests(r) for r in raw)
    assert {decode(x) for x in both}==classes
    # Any full graph flattening of the physical and service consumers must
    # retain every distinct section, since each coordinate is a test.
    # Here the made-available target carrier is all described capability records
    # over all effects from the declared fixture, including undeclared combinations.
    universe={(a,kind,raw[0]['receipt']) for a in z['requests'].values() for kind in (False,True)
              if not kind or a in (None,z['requests']['maintenance'])}
    assert both<=universe
    assert {decode(x) for x in universe}==classes
    def lookup(n,m,c):return next(tests(x) for x in raw if x['case']==(n,m,c))
    assert (False,True,False,("OPEN",0))==lookup('in','first',False)==lookup('in','volatile_split',True)
    assert not any(lookup(n,'split',c)[0] or lookup(n,'split',c)[1] for n,c in product(z['requests'],(False,True)))
    assert lookup('maintenance','split',True)[2] and not lookup('maintenance','envelope',True)[2]
    # Separate sweep-based direct calendar: release a closed integer
    # interval only at upper endpoint plus one. Compare all test results.
    def sweep(closure, occupied):
        if closure is None:return False
        active=[0,0]
        ev=sorted((t,j,d) for j,(a,b) in enumerate((closure,occupied))
                          for t,d in ((a,+1),(b+1,-1)))
        for t in sorted(set(x[0] for x in ev)):
            for _,j,d in (e for e in ev if e[0]==t):
                active[j]+=d
            if all(active):return True
        return False
    for row in raw:
        eff,service,receipt=take(row)
        assert tests(row)==(*(sweep(eff,w) for w in windows),bool(eff and service),receipt)
    return dict(cases=len(raw),classes=len(classes),capability_records=len(universe),
                snapshot_classes=1,stale_collisions=sum(any(r["contact"]) for r in raw if r["case"][1]=="snapshot"),
                gate_keep_gap_us=z["hulls"][1][0]-z["hulls"][0][1],
                max_egress_limit_us=454*S)
for gate in range(2):
    z=generate(gate)
    print(json.dumps(dict(gate=gate,**{k:v for k,v in z.items() if k!="requests"},
                          **evaluate(z)),sort_keys=True))
