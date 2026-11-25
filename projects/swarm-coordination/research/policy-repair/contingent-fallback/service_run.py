"""Actual occupancy/action control, not merely match feasibility."""
from live import *

def execute(T,pick):
    # Independent direct algorithm at the fallback cut. Job uses helper 0
    # on ticks 2--4 inclusive; the pre-existing unrelated tail uses helper 3.
    M={(C[0].received if C[0].notice_at<=4 else ()):
                    perfect(common(C,{0} if pick else ())) for C in partition(T)}
    receipt={key:res for key,res in M.items()}
    journals=[]
    for t in T:
        key=t.received if t.notice_at<=4 else ()
        action=receipt[key]
        if action is None:return None
        used=defaultdict(set);done=[]
        for q in range(7):
            actual=set(t.old_active) if q<6 else set()
            if pick and 2<=q<5:
                if 0 in actual or 0 in t.failed:return None
                actual.add(0)
            if 4<=q<6:
                for i,x in enumerate(action):
                    if x not in t.viable[i] or x in (actual|t.failed|t.denied):return None
                    actual.add(x)
            used[q]=actual
            if pick and q==4:done.append(("optional",5))
        done.extend([("foreground0",6),("foreground1",6),("retained",6)])
        journals.append(done)
    return journals

def run():
    for lag,signal,fail in product(range(3),(False,True),(False,True)):
        T,H=authored(lag,signal,fail)
        plain=execute(T,False);assert plain
        optimal=execute(T,True)
        assert bool(optimal)==(0 in released(T,H))
        assert all(len(u)==(4 if optimal else 3) for u in (optimal or plain))
    T,H=authored()
    T2,_=authored(second_loss=True)
    assert execute(T,True) and not execute(T+T2,True) and execute(T+T2,False)
    print("12 actual foreground/reserve occupancy mission comparisons")
    print("during bounded repair, timely checked migration settles 4 jobs, guarded fallback settles 3")
    print("under admitted late second loss, 3 still settle; a blanket global lock is unnecessary")
if __name__=="__main__":run()
