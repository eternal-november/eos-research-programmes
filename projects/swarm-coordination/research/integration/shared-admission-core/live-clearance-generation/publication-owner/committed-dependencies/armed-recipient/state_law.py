"""Independent finite safety projection, not a scheduler, timing model or SQL refinement proof."""
from collections import deque
from dataclasses import dataclass,replace
import json

@dataclass(frozen=True)
class State:
    a_arm:bool=False
    a_installed:bool=False
    a_closed:bool=False
    a_effect:bool=False
    selected_b:bool=False
    arm_b:bool=False
    copy_b:int=-1 # untouched, copied without this receipt, copied with this receipt
    open_b:bool=False
    b_effect:bool=False

def edge(s,arm_gate=True,local_gate=True,fresh_copy=True):
    if not (s.selected_b or s.a_arm):
        yield "issue-A",replace(s,a_arm=True)
    if s.a_arm and not s.a_installed and (not s.a_closed or not local_gate):
        # Removing the actual local barrier can re-open a blocked A.
        yield "install-A",replace(s,a_installed=True,a_closed=False)
    if s.a_installed and not s.a_closed and not s.a_effect:
        yield "commit-A",replace(s,a_effect=True)
    if not s.a_closed:
        yield "close-A-local",replace(s,a_closed=True)
    if not s.selected_b and (not s.a_arm or s.a_closed or not arm_gate):
        yield "select-B",replace(s,selected_b=True)
    if s.selected_b and not s.arm_b:
        yield "issue-B",replace(s,arm_b=True)
    if s.selected_b and s.copy_b==-1:
        yield "copy-B",replace(s,copy_b=int(s.a_effect and fresh_copy))
    if s.arm_b and s.copy_b>=0 and not s.open_b:
        yield "install-B",replace(s,open_b=True)
    if s.open_b and s.copy_b==0 and not s.b_effect:
        yield "commit-B",replace(s,b_effect=True)

def scan(**switch):
    root=State()
    q=deque([root])
    prev={root:None}
    steps=0;best=None
    while q:
        s=q.popleft()
        if s.a_effect and s.b_effect and best is None:
            trace=[]
            t=s
            while prev[t]:
                t,act=prev[t]
                trace.append(act)
            best=list(reversed(trace))
        for name,t in edge(s,**switch):
            steps+=1
            if t not in prev:
                prev[t]=(s,name)
                q.append(t)
    return len(prev),steps,best

def main():
    ans={"typed":scan(),"missing_arm_gate":scan(arm_gate=False),
         "missing_local_gate":scan(local_gate=False),"stale_donor_copy":scan(fresh_copy=False)}
    assert ans["typed"][2] is None
    assert all(ans[x][2] for x in ans if x!="typed")
    print(json.dumps(ans,sort_keys=True,separators=(",",":")))
if __name__=="__main__":main()
