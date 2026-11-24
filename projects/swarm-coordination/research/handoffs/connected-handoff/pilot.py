"""Bounded, asynchronous connected support handoff. Python 3.12."""
import argparse
from itertools import product
import json


def setup(n, live, keep_suffix=False):
    """Run admitted placements and witnessed ordinary suffix settlements."""
    assert 1 <= live <= n
    stock = [None] * (n + 1)
    trace = []
    for j in range(n):
        assert stock[j] is None
        stock[j] = j
        trace.append((-2, "place_on_native_support", j))
    for j in range(live,n):
        if keep_suffix and j == n-1 and j > live:
            continue
        assert stock[j] == j
        stock[j] = None   # The task now rests on its fixed final rack.
        trace.append((-1, "settled_on_fixed_rack", j))
    trace.append((0, "root_requests_relief", 0))
    return stock, trace


def run(n, live, hop_delays, deadline, terminal_unavailable=False, keep_suffix=False):
    """Each call chooses inputs, not policy; no crew receives 'live'."""
    assert len(hop_delays) == n and min(hop_delays) >= 1
    stock, events = setup(n,live,keep_suffix)
    live_tasks = sorted(x for x in stock if x is not None)
    received, inbox = {0:0}, {}
    granted = {}
    used = set()
    completed = None
    down = {live} if terminal_unavailable else set()

    def send(t, sender):
        # Local station has at most one successor in the installed layout.
        if sender == n:
            return
        peer = sender + 1
        inbox.setdefault(t + hop_delays[sender], []).append(peer)
        events.append((t, "send_authorization", (sender,peer)))

    send(0,0)
    for t in range(deadline + 1):
        # 1. Outstanding transfers accept while the old support remains
        # intact; only actual acceptance makes its support stock free.
        for source, target, task in sorted(granted.pop(t,[])):
            assert stock[source] == task and stock[target] is None
            stock[source], stock[target] = None, task
            used.update((source,target))
            events.append((t,"accepted_support",(source,target,task)))
            if source == 0:
                completed = t
        assert sorted(x for x in stock if x is not None) == live_tasks
        assert all(j is None or i in (j,j+1) for i,j in enumerate(stock))
        # 2. Deliver notices. A still-busy native holder forwards once;
        # a free receiver retains the authorization but does not forward.
        for i in inbox.pop(t,[]):
            assert i not in received
            received[i] = t
            events.append((t,"received_authorization",i))
            if stock[i] == i:
                send(t,i)
        # 3. A locally authorized, free receiver occupying no grant may
        # begin the one-slot acceptance of its predecessor's load.
        claimed = set()
        for i in range(1,n+1):
            j = i-1
            if (stock[i] is None and stock[j] == j and i in received and i not in down
                    and i not in claimed and j not in claimed and t < deadline):
                grant = (j,i,j)
                granted.setdefault(t+1,[]).append(grant)
                claimed.update((i,j))
                events.append((t,"begin_transfer",grant))
        if completed is not None:
            break

    return dict(safe=True, relieved=completed is not None, release_tick=completed,
                touched=sorted(used), final=stock, trace=events)


def matching(n, live, terminal_unavailable=False):
    """Enumerate all endpoint assignments of live loads away from root."""
    forbidden = {0,live} if terminal_unavailable else {0}
    return [
        holders for holders in product(*[(j,j+1) for j in range(live)])
        if all(i not in forbidden and 0 <= i <= n for i in holders)
        and len(set(holders)) == live
    ]


def earliest_reference(n, live, authorized_at, terminal_unavailable=False):
    """Independent BFS over support placements; no simulator calls."""
    noload = n+1
    states = {tuple(list(range(live)) + [noload]*(n+1-live))}
    seen = set()
    # Authorization only delays; a complete path cannot require more than n
    # different one-hop transfers after the final new permission.
    for t in range(max(authorized_at, default=0)+n+1):
        if any(x[0] == noload for x in states):
            return t
        next_states = set(states)  # Source support can wait indefinitely.
        for placement in states:
            possible = [(j,j+1) for j in range(n) if placement[j] == j
                        and placement[j+1] == noload and t >= authorized_at[j]
                        and not (terminal_unavailable and j+1 == live)]
            for move in product((False,True), repeat=len(possible)):
                dest = list(placement)
                picked = [p for p,yes in zip(possible,move) if yes]
                used = [i for pair in picked for i in pair]
                if len(used) != len(set(used)):
                    continue
                for j,k in picked:
                    dest[j], dest[k] = noload,j
                next_states.add(tuple(dest))
        if t >= max(authorized_at, default=0) and next_states <= seen:
            return None
        seen |= next_states
        states = next_states
    return None


def verify():
    out = []
    for n in range(1,8):
        for k in range(1,n+1):
            for delays in [(1,)*n,(2,)*n,tuple(1+j%3 for j in range(n))]:
                receipts = [sum(delays[:i+1]) for i in range(n)]
                expected = receipts[k-1]+k
                assert matching(n,k) == [tuple(range(1,k+1))]
                assert matching(n,k,True) == []
                assert earliest_reference(n,k,[0]*n) == k
                assert earliest_reference(n,k,receipts) == expected
                assert earliest_reference(n,k,receipts,True) is None
                for due in (expected-1,expected,expected+1):
                    r=run(n,k,delays,due)
                    assert r["relieved"] == (due >= expected)
                    if r["relieved"]:
                        assert r["release_tick"] == expected and r["touched"] == list(range(k+1))
                    else:
                        assert r["final"][0] == 0
                    if n == 3 and delays == (1,)*n:
                        out.append(dict(n=n,live=k,delay=list(delays),deadline=due,**r))
                assert not run(n,k,delays,expected+1,True)["relieved"]
    local_law = run(4,1,(1,1,1,1),4,keep_suffix=True)
    extended=run(4,2,(1,1,1,1),4,keep_suffix=True)
    for k,r in [(1,local_law),(2,extended)]:
        assert r["final"][3] == 3
        assert not any(e[1]=="send_authorization" and e[2][0]>=k for e in r["trace"])
    assert local_law["touched"] == [0,1] and extended["touched"] == [0,1,2]
    return dict(sweep_instances=84, trace_controls=out, equal_deadline_demonstration=[
        dict(live=1,deadline=4,**local_law),dict(live=2,deadline=4,**extended)])


if __name__ == "__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--json",action="store_true")
    out=verify()
    if p.parse_args().json:
        print(json.dumps(out,indent=2,sort_keys=True))
    else:
        print("84 bounded configurations: endpoint matching, timing oracle, and local traces agree.")
        for row in out["equal_deadline_demonstration"]:
            print(f'{row["live"]} live loads: support from crews {row["touched"]}; root relieved at {row["release_tick"]} by deadline {row["deadline"]}')
