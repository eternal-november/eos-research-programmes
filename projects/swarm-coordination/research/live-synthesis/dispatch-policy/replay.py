"""Exact Boolean controller synthesis for a lab warehouse fixture model."""
from itertools import product
import json

def dot(r,v):
    return (r&v).bit_count()%2

def apply(a,v):
    return sum(dot(r,v)<<i for i,r in enumerate(a))

def all_matrices(n):
    positions=[(i,j) for i in range(n) for j in range(i)]
    for bits in range(1<<len(positions)):
        a=[1<<i for i in range(n)]
        for k,(i,j) in enumerate(positions):
            a[i] |= ((bits>>k)&1)<<j
        yield tuple(a)

def compile_inverse(a):
    """Triangular GF(2) solve, returns straight-line row coefficient policy."""
    b=[]
    for i,r in enumerate(a):
        assert r>>i==1
        s=1<<i
        for j in range(i):
            if (r>>j)&1:
                s ^= b[j]
        b.append(s)
    return tuple(b)

def multiply(a,b):
    return tuple(reduce_xor(b[j] for j in range(len(b)) if (r>>j)&1) for r in a)

def reduce_xor(xs):
    s=0
    for x in xs:
        s ^= x
    return s

def exact_reference(a,y):
    """Enumerate possible actual latch vectors, independently of synthesis."""
    candidates=[v for v in range(1<<len(a))
                if all(sum(((row>>j)&1)*((v>>j)&1) for j in range(len(a)))%2
                       == ((y>>i)&1) for i,row in enumerate(a))]
    assert len(candidates)==1
    return candidates[0]

def simulate(a,h,*,chosen='synthesis',hold=True,latest=None,ready=True,bank=(),probe_limit=None,bad=False):
    """Trace of an old timed commitment and optional newly qualifying dispatch."""
    n=len(a)
    D=100*n**3+100
    identity=tuple(1<<i for i in range(n))
    active=(1,a)
    # Independent support P is still leased to the earlier load. Optional
    # work on Q occupies it through the fast cut unless Q is preserved.
    station={'P':'old','Q':None if hold else 'optional'}
    events=[[-1,'accept-old-P',D], [0,'authority-publish',1],
            [0,'preserve-Q' if hold else 'admit-optional-Q',D+1]]
    candidate=None
    if chosen=='synthesis' and ready:
        b=compile_inverse(a)
        if bad:
            b=(b[0]^1,*b[1:])
        if multiply(a,b)==identity:
            candidate=(1,b)
            events.append([D-1,'checked-candidate',1])
        else:
            events.append([D-1,'rejected-invalid-candidate',1])
    if latest is not None:
        assert latest!=a
        active=(2,latest)
        events.append([D-1,'authority-replace',2])
    events.append([D,'old-release-P',1])
    assert station['P']=='old'
    station['P']=None
    y=apply(active[1],h)
    events.append([D,'observe-local-latches',y])
    if chosen=='library' and ready and latest is None:
        # Lookup by exact authenticated matrix, no online code compilation.
        candidate=next(((1,b) for label,b in bank if label==a),None)
    if candidate is not None and candidate[0]==active[0] and station['Q'] is None:
        events.append([D,'activate',active[0]])
    else:
        candidate=None
        events.append([D,'remain-fallback',active[0]])
    if chosen=='bounded' and station['Q'] is None and latest is None and ready:
        # A maximally permissive scalar-plan reference: on the read bits,
        # choose now only if *all* completions agree on the exact action.
        k=n-1 if probe_limit is None else probe_limit
        readmask=(1<<k)-1
        possible={exact_reference(a,v) for v in range(1<<n) if v&readmask==y&readmask}
        x=next(iter(possible)) if len(possible)==1 else None
    else:
        x=None if candidate is None else apply(candidate[1],y)
    fast=False
    if x is not None:
        assert x==h, 'fast dispatch would be rejected by physical guard'
        if station['Q'] is None:
            station['Q']='fast-load'
            fast=True
            events.append([D,'fast-accepted',x])
    if not hold:
        assert station['Q']=='optional'
        station['Q']=None
        events.append([D+1,'optional-release',0])
    events.append([D+1,'new-expedited-complete' if fast else 'new-standard-route',0])
    # Standard loading path is independent; no false deadline credit.
    if not fast:
        events.append([D+2,'new-standard-complete',0])
    return events, fast

def main():
    count=0
    outcomes={}
    for n in (1,2,3,4):
        mats=list(all_matrices(n))
        fs=set()
        for a in mats:
            b=compile_inverse(a)
            identity=tuple(1<<i for i in range(n))
            assert multiply(a,b)==multiply(b,a)==identity
            fs.add(tuple(apply(b,y) for y in range(1<<n)))
            for h in range(1<<n):
                y=apply(a,h)
                assert apply(b,y)==exact_reference(a,y)==h
                assert simulate(a,h)[1]
                assert not simulate(a,h,chosen='bounded')[1]
                assert simulate(a,h,chosen='library',bank=((a,b),))[1]
                assert not simulate(a,h,chosen='library',bank=())[1]
                assert not simulate(a,h,hold=False)[1]
                assert not simulate(a,h,ready=False)[1]
                assert not simulate(a,h,bad=True)[1]
                assert simulate(a,h,chosen='bounded',probe_limit=n)[1]
                if len(mats)>1:
                    latest=next(x for x in mats if x!=a)
                    assert not simulate(a,h,latest=latest)[1]
                count+=1
        assert len(fs)==2**(n*(n-1)//2)
        outcomes[str(n)]={"matrices":len(mats),"distinct_installed_responses":len(fs),
                         "matrix_state_pairs":len(mats)*(1<<n)}
    a=tuple(all_matrices(3))[-1]; h=5
    controls={name:simulate(a,h,**kw)[0] for name,kw in
              [('compiled',{}),('capacity-spent',{'hold':False}),
               ('timeout',{'ready':False}),('invalid',{'bad':True}),('stale',{'latest':tuple(all_matrices(3))[0]}),
               ('bounded',{'chosen':'bounded'}),('budget-raised-oracle',{'chosen':'bounded','probe_limit':3})]}
    print(json.dumps({"pairs":count,"dimension":outcomes,"events":controls},
                     sort_keys=True,indent=1))
if __name__=='__main__':
    main()
