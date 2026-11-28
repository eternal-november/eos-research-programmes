from collections import Counter
from itertools import product
from pathlib import Path
from subprocess import run
import sys
root=Path(__file__).resolve().parent
def records():
    states=list(product((0,1),(0,1),range(1,6),(0,1),(0,1,2,4,12,15,16,20)))
    inp=''.join(f'{i} '+' '.join(map(str,s))+'\n' for i,s in enumerate(states))
    p=run([sys.executable,root/'run.py'],input=inp,text=True,capture_output=True,check=True)
    ans={}
    for line in p.stdout.splitlines():
        i,n,*raw=map(int,line.split())
        c,l,t,on,value=states[i]
        assert n==on
        expected=(t,(value if 2<=value<16 else -999 if value<2 else 999) if c else 0) if on else None
        ans[(c,l,t,on,value)]=tuple(raw) if n else None
        assert ans[(c,l,t,on,value)]==expected
    assert len(ans)==len(states)
    return ans

R=records()
stats=Counter()
for deadline,pre_auth,close_park,camera_fault,time_post,old_pose,post_pose,scope in product(
    (2,3,4,5),(0,1),(0,1),(0,1),(2,3,4),(0,4),(0,4,16),(0,1)):
    # New duty announced at 2. Only authorized ready evidence in the
    # current parked episode and before deadline can service it.
    changed=bool(close_park)
    admissible_pre=bool(pre_auth and not changed)
    # The logical-only outage disables the ordinary post path. A single
    # RGB-D camera alternative may also exploit any equally authorized prior view.
    logic=admissible_pre
    pre_rgb=R[1,1,1,1,old_pose]
    post_rgb=R[1-camera_fault,0,time_post,1,post_pose]
    def decoded(m):
        # One visible designated part at the calibrated principal ray,
        # with known orientation in the selected pose fixture.
        return m is not None and 2<=m[1]<16
    kept=admissible_pre and decoded(pre_rgb)
    fresh=bool(scope and decoded(post_rgb) and post_rgb[0]<=deadline)
    rgb=kept or fresh
    stats['cases']+=1
    stats['logical_stage_succeeds']+=logic
    stats['same_cost_rgbd_succeeds']+=rgb
    stats['rgbd_only']+=rgb and not logic
    stats['stage_only']+=logic and not rgb
    stats['apparently_fresh_but_blank']+=camera_fault and post_rgb[0]<=deadline
    if old_pose==4 and not camera_fault and post_pose==4 and scope:
        assert not logic or rgb
        stats['shared_geometry_scope']+=1
        stats['strict_rgbd_extra_service']+=rgb and not logic
assert R[1,0,3,1,4]==(3,4) and R[0,0,3,1,4]==(3,0)
assert R[1,0,3,1,4]==R[1,1,3,1,4]
print(len(R),'native depth frame/flag cases')
print(dict(sorted(stats.items())))
