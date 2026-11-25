"""An access observation, before the expensive probe, chooses another station."""
from source import *
from factored import structured

def authored(w,D,B):
    s,stock=phase0(w);stage=None
    events=[]
    first=Q1
    for t in range(2,D):
        p,adjacent,blocked,failed,held,done,read=observe(w,s)
        if t==2:a=first
        elif t==3:
            # Serve only the actual directed local connection to Q, else return.
            stage=Q if Q in adjacent else P
            a=Q if stage==Q else J
        elif t==4 and stage==P:a=P
        elif p==stage and not read:a=PROBE
        elif p==stage and not done:
            a=(FORWARD,1,2) if failed==0 else (FORWARD,0,1)
        elif p==Q:a=Q1
        elif p in (P,Q1):a=J
        elif p==J and done:a=R if blocked==L else L
        elif p in (L,R):a=BASE
        elif p==BASE:a=WAIT
        else:return None
        if a not in options(w,s,t,B,3):return None
        s=effect(w,s,a,t,stock)
        if s is None:return None
        events.append((t,p,a,s))
    return events if s.pos==BASE and s.delivered else None

if __name__=="__main__":
    W=tuple(World(exit,loss,q_open=branch,p_aux=not branch) for branch in (True,False)
            for exit,loss in [(L,0),(R,2)])
    assert structured(W,10,7) is None # frozen first station not complete here
    assert plan(W,10,7,trace=True)
    assert not plan(W,9,7)
    assert not plan(W,10,6)
    for w in W:
        row=authored(w,10,7)
        assert row
        print(w.blocked,"before-source path selected",[(t,p,a) for t,p,a,s in row])
    print("access-dependent station selection gives exact report time 7 and egress 10")
    correlated=(W[0],W[3])
    assert plan(correlated,7,5,trace=True)
    assert not plan(correlated,6,5)
    assert not plan(correlated,7,4)
    print("if access itself determines both facts, first inspection is enough and no powered probe is needed")
    reversible=tuple(World(e,f,release_feed_on_departure=True)
                     for e,f in [(L,0),(R,2)])
    assert plan(reversible,8,6,trace=True)
    assert not plan(reversible,7,6)
    assert not plan(reversible,8,5)
    print("if leaving P really restores the slot, early departure restores egress at 8 and reports at 6")
