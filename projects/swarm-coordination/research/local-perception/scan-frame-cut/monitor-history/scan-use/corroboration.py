"""Exact model of distinct-acquisition release evidence, not the native policy."""
from itertools import product
from bisect import bisect_right
import json

def step(state,seq,hit,n):
    newest,count=state
    assert seq>=newest
    if hit: return seq,0
    return seq,min(n,count+(seq>newest))

def direct(events,n):
    newest=-1
    post=[]
    hits=-1
    invent=[]
    for i,(seq,hit) in enumerate(events):
        if hit: hits=i
        if seq>newest and not hit: invent.append(i)
        newest=seq
        post.append((newest,min(n,len(invent)-bisect_right(invent,hits))))
    return post

def run(n,events):
    state=(-1,0)
    ans=[]
    for seq,hit in events:
        state=step(state,seq,hit,n)
        ans.append(state)
    return ans

def replay():
    # Native evaluations and a separate evidence contract have different consumers.
    assert run(2,[(0,False),(0,False)])[-1][1]==1
    # Dropping all uses of the same acquisition removes a real current veto.
    assert run(2,[(0,False),(2,False)])[-1][1]==2
    assert run(2,[(0,False),(0,True),(2,False)])[-1][1]==1
    assert run(2,[(0,True),(0,False),(2,False)])[-1][1]==1
    exhaustive=0
    for n,k in product(range(1,5),range(1,8)):
        for trace in product(list(product((False,True),repeat=2)),repeat=k):
            seq=0;events=[]
            for advance,hit in trace:
                seq+=advance
                events.append((seq,hit))
            assert run(n,events)==direct(events,n)
            exhaustive+=1
    return dict(exact_trace_comparisons=exhaustive,old_id_current_veto=True,repeat_is_not_corroboration=True)

if __name__=='__main__':
    print(json.dumps(replay(),sort_keys=True,indent=2))
