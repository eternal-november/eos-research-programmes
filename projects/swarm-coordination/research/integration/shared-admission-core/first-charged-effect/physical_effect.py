"""Native RWARE fixture: one source-loop selector, rights fixed across one commit."""
import ctypes
import sys
from pathlib import Path
import numpy as np

# Source loader is the parent #804 fixture (verified by the run driver).
sys.path.insert(0,str(Path(__file__).resolve().parent))
import support

def bridge(path):
    c=ctypes.CDLL(str(path))
    callback=ctypes.CFUNCTYPE(ctypes.c_bool,ctypes.c_size_t)
    action=ctypes.CFUNCTYPE(None,ctypes.c_size_t)
    d=c.dispatch
    d.argtypes=(ctypes.c_size_t,callback,action)
    d.restype=ctypes.c_bool
    def apply(inspect,commit):
        return d(2,callback(inspect),action(commit))
    return apply

def episode(iso,n,choose,pre,post,arm):
    w=iso.make(n,False)
    # Native step is still constrained to exactly one FORWARD request;
    # the exhausted opportunity is one invocation, including a refusal.
    w.shelfs=[];w.goals=[];w.request_queue=[]
    w.n_agents=4
    n.Agent.counter=0
    q,l,r,observer=(n.Agent(2,pre+1,n.Direction.DOWN if pre==0 else n.Direction.UP,0),
                    n.Agent(1,1,n.Direction.RIGHT,0),
                    n.Agent(1,2,n.Direction.RIGHT,0),
                    n.Agent(4,4,n.Direction.LEFT,0))
    w.agents=[q,l,r,observer]
    w.grid=np.zeros((2,5,5),dtype=int)
    w._recalc_grid()
    act=n.Action
    def step(a):
        n.step(w,[x.value for x in a])
    def free(k):return not w.grid[0,k+1,2]
    plan=0 if free(0) else 1
    assert plan==1-pre
    # An actual independent movement happens in all runs, before service.
    step([act.NOOP,act.NOOP,act.NOOP,act.FORWARD])
    assert support.pos(observer)==(3,4)
    # An admitted old-carrier return changes which replacement is feasible.
    if post==2:
        # Both claimed: allocate another stationary carrier to the free slot
        # as explicit initial-at-cut authority conflict, not fabricated motion.
        blocker=n.Agent(3,2-pre,n.Direction.LEFT,0)
        w.agents.append(blocker);w.n_agents+=1;w._recalc_grid()
        step([act.NOOP]*4+[act.FORWARD])
        assert support.pos(blocker)==(2,2-pre)
    else:
        step([act.NOOP if pre==post else act.FORWARD]+[act.NOOP]*3)
        assert support.pos(q)==(2,post+1)
    assert (bool(free(0)),bool(free(1)))==((post==1),(post==0))
    before=w._cur_steps
    did=[]
    def commit(k):
        did.append(k)
        actions=[act.NOOP]*w.n_agents
        actions[k+1]=act.FORWARD
        step(actions)
    if arm==0:choose(free,commit)
    elif arm==1:commit(plan)
    elif arm==2:commit(0)
    elif arm==3:commit(1)
    else:
        if free(0):commit(0)
        elif free(1):commit(1)
    paid=(support.pos(l)==(2,1))+(support.pos(r)==(2,2))
    assert paid<=1 and support.pos(observer)==(3,4)
    assert w._cur_steps==before+bool(did)
    return paid,1,len(did)
