"""Civil warehouse load support: event plant and installed local policies."""
import json
from itertools import product
from collections import defaultdict
from original import setup, run as original_run

DEADLINE = 5
ARMS = ((False, False), (True, False), (False, True), (True, True))

def simulate(live, hop_fault, dwell_fault, preissue, before=True, deadline=5, buggy=False):
    stock, trace = setup(4, live, True)
    # Rack placements are executed by the pinned source. The request is emitted by this plant at 0.
    assert trace.pop() == (0, "root_requests_relief", 0)
    trace = [list(e) for e in trace]
    live_ids = sorted(x for x in stock if x is not None)
    wire = []
    auth = {}
    pending = []
    completion = None
    obs = defaultdict(list)
    def event(t, tag, *data):
        trace.append([t, tag, *data])
    # Root authorization is specific to the committed maintenance order and load.
    # It permits preparations before 0, but no downstream dispatch before 0.
    def send(t, src, token, jam=False):
        wire.append((t + 1 + int(jam and src == 0), src, token))
        obs[src].append([t, 'send', src+1, token])
        event(t, 'send', src, src+1, token)
    token = (0, 'maintenance-0', 0)
    obs[0].append([-1, 'local_root_commitment', token])
    event(-1, 'local_root_commitment', token)
    if preissue:
        send(-1, 0, token)
    def deliver(t):
        chosen = [x for x in wire if x[0] == t]
        for due, src, tok in chosen:
            wire.remove((due,src,tok))
            idx = src+1
            assert idx not in auth and t >= tok[2]
            auth[idx] = tok
            obs[idx].append([t, 'receive', src, tok, stock[idx]])
            event(t, 'receive', idx, tok)
            if stock[idx] == idx:
                send(t, idx, tok)
    for t in range(deadline + 3):
        # Physical acceptance happens before the next request on either endpoint.
        for grant in [g for g in pending if g[0] == t]:
            _, a, b, job = grant
            pending.remove(grant)
            assert stock[a] == job and stock[b] is None, ("stale_acceptance", t, grant)
            stock[a], stock[b] = None, job
            obs[a].append([t, 'relieved', b, job])
            obs[b].append([t, 'accepted', a, job])
            event(t, 'accept', a, b, job)
            if a == 0:
                completion = t
        if t == 0:
            event(t, 'root_requests_relief', 0)
            if not before:
                deliver(t)
            if hop_fault:
                # A transient queue delay moves only due packets on 0->1.
                # An issue in the tick-0 request phase also sees the delay.
                wire[:] = [(1 if due == 0 and src == 0 else due, src, tok)
                           for due, src, tok in wire]
                event(t, 'hop_fault_onset')
            if dwell_fault:
                event(t, 'dwell_fault_onset')
            if not preissue:
                send(t,0,token,hop_fault)
        if t or before:
            deliver(t)
        # Different arm inputs are unavailable to controller predicates. Physical
        # plant, not dispatch, determines actual duration. Earlier grants stay live.
        claimed = set() if buggy else {i for _,a,b,_ in pending for i in (a,b)}
        for b in range(1,5):
            a = b-1
            if b in auth:
                obs[b].append([t, 'ready_check', stock[a], stock[b], a in claimed, b in claimed])
            if (t < deadline and auth.get(b) == token and stock[a] == a and
                    stock[b] is None and a not in claimed and b not in claimed):
                dt = 1 + int(dwell_fault and b == 2)
                pending.append((t+dt,a,b,a))
                claimed.update((a,b))
                event(t,'begin',a,b,a)
        assert sorted(x for x in stock if x is not None) == live_ids and stock[3]==3
        assert all(load is None or i in (load,load+1) for i,load in enumerate(stock))
        if t == deadline:
            event(t, 'service_cut', tuple(stock), tuple(pending), completion)
        if not buggy:
            assert len({i for _,a,b,_ in pending for i in (a,b)}) == 2*len(pending)
            assert all(stock[a]==job and stock[b] is None for _,a,b,job in pending)
    return dict(completion=completion, served=completion is not None and completion<=deadline,
                final=stock, trace=trace, local=dict(obs), refused=False)

def reference(live, h, d, early, before, deadline):
    """Enumerate lawful activation/acceptance starts under fixed authority and no bypass."""
    if early:
        at1 = int(h and before)
    else:
        at1 = 1 + int(h)
    if live == 1:
        feasible = [x+1 for x in range(deadline) if x >= at1]
    else:
        feasible = [x+1 for j,x in product(range(deadline),repeat=2)
                    if j >= at1+1 and x >= j+1+int(d)]
    return min(feasible,default=None)

def main():
    rows=[]
    for live,early,before,(h,d),deadline in product((1,2),(False,True),(True,False),ARMS,(4,5,6)):
        r=simulate(live,h,d,early,before,deadline)
        assert r['completion'] == reference(live,h,d,early,before,deadline)
        if not h and not d and not early:
            q=original_run(4,live,[1]*4,deadline,keep_suffix=True)
            assert q['release_tick']==r['completion'] and q['final']==r['final']
        rows.append(dict(live=live,preissue=early,fault_before_due=before,hop=h,dwell=d,deadline=deadline,**r))
    try:
        simulate(2,False,True,False,buggy=True)
    except AssertionError as e:
        assert e.args[0][:2]==('stale_acceptance',5)
    else:
        raise AssertionError('did not reproduce stale acceptance')
    assert [simulate(2,h,d,False)['completion'] for h,d in ARMS] == [4,5,5,None]
    assert [simulate(2,h,d,True)['completion'] for h,d in ARMS] == [3,4,4,5]
    assert [simulate(2,h,d,True,False)['completion'] for h,d in ARMS] == [3,3,4,4]
    assert [simulate(1,h,d,False)['completion'] for h,d in ARMS] == [2,3,2,3]
    pending = next(e[2:] for e in simulate(2,True,True,False,deadline=4)['trace']
                   if e[1] == 'service_cut')
    assert pending[1] == ((5,1,2,1),) and pending[2] is None
    print(json.dumps(dict(cases=rows,stale_acceptance_regression=True),sort_keys=True,indent=1))

if __name__ == '__main__': main()
