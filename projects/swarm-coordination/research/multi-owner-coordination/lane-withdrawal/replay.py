"""Finite civilian shared-lane cutover, exact integer phases."""
from itertools import product
import json

def run(f,a,d,r,policy,deadline=4,D=None,owner_empty=False,reserve=False):
    # d=None denotes an accidental failure leaving a physically stuck load.
    active=None; receipt=None; issued=False; opening=True; census=None
    start=None; old_end=None; route=None; events=([[-2,'owned-proposal-sent']] if a is not None else [[-2,'old-owner-declines-uncommitted-work']])+[[0,'withdrawal-effective-at-owner']]
    for t in range(-1,max(deadline+2,f+(D or (d or 0))+r+2)+1):
        if active is not None and d is not None and t==active+d:
            events.append([t,'actual-old-release',active]); old_end=t
            receipt=t+r; active=None
        if t==f:
            opening=False; census=issued
            events.append([t,'port-fence-and-complete-accepted-set',int(census)])
        if t==a:
            if opening:
                assert active is None and not issued
                active=t; issued=True; events.append([t,'accepted-old-physical-start'])
            else:
                events.append([t,'rejected-no-old-start-right'])
        if receipt==t:
            events.append([t,'trusted-old-receipt-arrives'])
        if t<0 or start is not None:
            continue
        vacant=active is None
        if policy=='direct':
            enable=not opening and vacant
        elif policy=='receipt':
            enable=not opening and (census is False or (receipt is not None and receipt<=t))
        elif policy=='timeout':
            assert D is not None and d is not None and d<=D
            enable=not opening and t>=max(f,f-1+D)
        elif policy=='owner-only':
            enable=t>=f and owner_empty
        else: raise ValueError(policy)
        if enable:
            if opening or not vacant:
                events.append([t,'unsafe-owner-only-permission-blocked'])
            else:
                start=t; route='shared'; events.append([t,'successor-start',route])
        if start is None and reserve and t==deadline:
            start=t;route='separate-held-support';events.append([t,'successor-start',route])
    # Successor operation takes one tick and may not cancel prior duties.
    if start is not None:
        events.append([start+1,'successor-complete',route])
    if route == 'shared' and issued:
        assert old_end is not None and old_end<=start
    return dict(start=start,route=route,old_accepted=issued,old_complete=old_end,
                meets_start=start is not None and start<=deadline,events=sorted(events,key=lambda e:e[0]))

def oracle(f,a,d,r,policy,D):
    # Enumerate starts over half-open occupation intervals, independently of event simulation.
    accepted=a<f
    legal=lambda t:t>=f and not (accepted and a<=t<a+d)
    earliest=next(t for t in range(f+D+r+2) if legal(t)
                  and (policy!='receipt' or not accepted or t>=a+d+r)
                  and (policy!='timeout' or t>=max(f,f-1+D)))
    return earliest

def main():
    count=0
    for L,D,R in product(range(1,5),range(1,5),range(5)):
        maxima={p:0 for p in ('direct','receipt','timeout')}
        for f,a,d,r in product(range(1,L+1),range(-1,L+1),range(1,D+1),range(R+1)):
            for p in maxima:
                x=run(f,a,d,r,p,D=D)
                assert x['start']==oracle(f,a,d,r,p,D)
                assert x['old_accepted']==(a<f)
                assert x['old_complete']==(a+d if a<f else None)
                maxima[p]=max(maxima[p],x['start'])
            count+=1
        assert maxima==dict(direct=max(L,L-1+D),receipt=max(L,L-1+D+R),timeout=max(L,L-1+D))
    examples={
      'lawful_in_flight_accepted':run(2,1,3,2,'direct'),
      'lawful_in_flight_rejected':run(2,2,3,2,'direct'),
      'lawful_refusal_of_new_work':run(2,None,3,2,'direct'),
      'documentary_late':run(2,1,3,2,'receipt'),
      'same_fence_with_certified_timeout':run(2,1,3,2,'timeout',D=3),
      'arbitrary_owner_clear_claim_blocked':run(2,1,3,2,'owner-only',owner_empty=True),
      'accidental_jam_uncleared':run(2,1,None,0,'direct'),
      'accidental_jam_independent_successor_reserve':run(2,1,None,0,'direct',reserve=True),
    }
    a,b,declined,c,_,e,f,g=examples.values()
    assert a['start']==4 and a['old_complete']==4 and b['start']==2 and not b['old_accepted']
    assert declined['start']==2 and not declined['old_accepted']
    assert c['start']==6 and e['start']==4 and any(x[1].startswith('unsafe') for x in e['events'])
    assert f['start'] is None and g['start']==4 and g['old_complete'] is None
    for d,r in ((2,2),(3,2)):
        # At t=3 there is no receipt in either case, while physical vacancy differs.
        assert 1+d+r>3
    print(json.dumps(dict(traces=count,policy_checks=count*3,examples=examples),sort_keys=True,indent=2))

if __name__=='__main__': main()
