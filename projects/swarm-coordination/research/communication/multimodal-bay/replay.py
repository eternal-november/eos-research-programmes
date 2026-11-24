"""Civil cargo bay: route handoff under changing local evidence."""
from itertools import product
import json

# All integer times. No old use or future start is possible once the old
# terminal drain condition holds. One old admission was closed before tick 0.
A_MAX=2
K_MAX=5
H=max(A_MAX,K_MAX)
DURATION=1
TOKEN=('upstream-A','downstream-B','bay-1',2,'job-B')
OLD=('upstream-A','downstream-B','bay-1',1,'job-B')
FORGED_CONTEXT=('upstream-A','downstream-B','bay-2',2,'job-B')
# (period, phase, transit): send/copy/poll at the first allowed cut and deliver
LINKS={
    'rf-duplex': (1,0,0), 'optical-forward': (1,0,1),
    'acoustic-forward': (1,0,2), 'dock-intermittent': (3,0,1),
    'persistent-marker': (2,0,0), 'interlock-read': (1,0,0),
    'reverse-only': None, 'partition': None, 'anonymous-beacon': None
}
LEAK_FREE=('reverse-only','partition','anonymous-beacon')

def deliver_time(mode,t):
    p=LINKS[mode]
    if p is None: return None
    period,phase,tr=p
    return t+(phase-t)%period+tr

def simulate(a,b,k,mode,deadline):
    # Old load admitted at -2 when present; it occupies disjoint staging
    # initially, then holds the exclusive bay from -1 until k.
    events=[[-2,'close-old-admissions'],[-2,'accept-new-service']]
    if k: events += [[-2,'vest-old-bay-use'],[-1,'old-enters']]
    wired=[]
    qualified=None
    notify_b=False
    switched_a=False
    sent=False
    published=False
    transferred=False
    finish=None
    old_live=bool(k)
    for t in range(max(H+6,deadline+2)):
        if old_live and t==k:
            old_live=False;events.append([t,'old-exits'])
        if t==a: switched_a=True;events.append([t,'notice-A'])
        if t==b: notify_b=True;events.append([t,'notice-B'])
        if t==0:
            events.append([0,'plant-switch-from-primary-rf',mode])
            # Plausible old messages, and a current-looking wrong bay.
            events.append([0,'B-reads-cached-records',OLD,FORGED_CONTEXT])
            assert OLD!=TOKEN and FORGED_CONTEXT!=TOKEN
        if switched_a and not old_live and not sent:
            sent=True;published=True;events.append([t,'drain-published'])
        link=LINKS[mode]
        if published and not transferred and link is not None:
            period,phase,transit=link
            if t%period==phase:
                transferred=True
                if mode=='interlock-read':
                    # This is a context-bound mechanical predicate at the
                    # decision cut, not a packet from A.
                    assert switched_a and not old_live
                    qualified=t
                    events.append([t,'B-reads-release-interlock'])
                else:
                    events.append([t,'B-samples-persistent-mark' if mode=='persistent-marker'
                                   else 'adapter-forwards-bound-record',mode])
                    wired.append((t+transit,TOKEN))
        if mode=='reverse-only' and t==b:
            events.append([t,'B-to-A-request-with-no-return-evidence'])
        if mode=='anonymous-beacon':
            events.append([t,'anonymous-unbound-beacon'])
        for _,token in [x for x in wired if x[0]==t]:
            events.append([t,'B-receives',token])
            if token==TOKEN: qualified=t
        if finish==t:
            events.append([t,'new-exits'])
        if finish is None and notify_b and (qualified is not None or t>=H):
            assert not old_live and switched_a
            events.append([t,'B-enters'])
            finish=t+DURATION
    return dict(finish=finish,serves=finish<=deadline,events=events)

def reference(a,b,k,mode):
    # Enumerate cuts at which A can attest, each physical contact/sample cut,
    # and then B's legally admissible entry slots without using replay state.
    p=LINKS[mode]
    receipt=[]
    if p is not None:
        period,phase,transit=p
        first_ready=next(t for t in range(H+1) if t>=a and t>=k)
        contact=next(t for t in range(2*H+4) if t>=first_ready and t%period==phase)
        receipt.append(contact+transit)
    return next(t+DURATION for t in range(2*H+4)
                if t>=b and (t>=H or any(r<=t for r in receipt)))

def local_hist(t,a,b,k,mode):
    arrival=deliver_time(mode,max(a,k))
    # Fixed stale and wrong-context records and unbound beacon match across all
    # compared worlds; only usable evidence and activation can vary.
    return tuple((x,'notice') for x in [b] if x<=t)+tuple(
        (x,'token') for x in [arrival] if x is not None and x<=t)

def main():
    count=0
    served={}
    for a,b,k,mode,d in product(range(A_MAX+1),range(4),range(K_MAX+1),LINKS,range(2,9)):
        out=simulate(a,b,k,mode,d)
        expected=reference(a,b,k,mode)
        assert out['finish']==expected and out['serves']==(expected<=d)
        served[mode]=served.get(mode,0)+out['serves'];count+=1
    cases={}
    for mode in LINKS:
        for k in (0,5):
            cases[mode+'/'+str(k)]=simulate(1,2,k,mode,4)
    # All local prefixes through the last admissible start at 3 are identical.
    for mode in LEAK_FREE:
        assert local_hist(3,1,2,0,mode)==local_hist(3,1,2,5,mode)
        assert not cases[mode+'/0']['serves'] and not cases[mode+'/5']['serves']
    # Same new service, same old job and local detections across successful
    # modalities; only the transfer and sampling phases differ.
    matched={m:simulate(1,2,2,m,5) for m in LINKS}
    assert all(matched[m]['serves'] for m in LINKS if LINKS[m] is not None)
    assert all(not matched[m]['serves'] for m in LEAK_FREE)
    # Validate a full transcript class exact earliest safe cut in absence.
    for t in range(H+1):
        belief=[(a,k) for a,k in product(range(A_MAX+1),range(K_MAX+1))
                if local_hist(t,a,2,k,'partition')==local_hist(t,1,2,0,'partition')]
        assert all(a<=t and k<=t for a,k in belief)==(t>=H)
    print(json.dumps(dict(checks=count,served=served,deadline4_cases=cases,matched_mode_cases=matched),
                     indent=1,sort_keys=True))
if __name__=='__main__': main()
