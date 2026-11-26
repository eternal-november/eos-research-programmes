from itertools import product
import json
import subprocess
import sys

# All event times are exact binary floats in the native fixture.
rows=[(cap,s,r,mode,hold,lost_rival,lost_duty)
      for cap in range(2,9) for s in range(1,cap+1) for r in range(1,cap+1)
      for mode, hold, lost_rival, lost_duty in product(range(4),range(4),range(2),range(2))]
controls={}
proc=subprocess.run([sys.argv[1]],input=''.join(' '.join(map(str,x))+'\n' for x in rows),
                    text=True,check=True,capture_output=True)
found=proc.stdout.splitlines()
assert len(found)==len(rows)
for p,line in zip(rows,found):
    cap,s,r,mode,hold,erased,lost=p
    allow=hold in (0,2) or not mode or s+r<=cap
    has_tx=bool(mode&1) and allow
    has_rx=bool(mode&2) and allow and not erased
    late=not lost and (s+r<=cap or not (has_tx or has_rx))
    row=tuple(map(int,line.split()))
    assert row==(4,4*late,4*(allow and not erased),4,8),(p,row)
    if p in [(5,3,3,1,0,0,0),(5,3,3,2,0,1,0),(5,3,3,2,1,0,0),
             (5,3,3,2,2,0,0),(5,3,3,2,3,0,0),(5,3,3,2,1,0,1),
             (5,2,3,3,1,0,0),(5,3,3,0,1,0,0)]:
        # In this model the unique unpaid infinite word repeats both cuts.
        # Every such word sees E infinitely, so strong unpaid is impossible.
        strong_unpaid=False
        weak_unpaid=(row[1]==0)  # true at open, so only late can be disabled
        controls[','.join(map(str,p))]=dict(open_enabled=row[0],late_enabled=row[1],
            rival_delivery=row[2],independent_delivery=row[3],
            weak_unpaid=weak_unpaid,strong_unpaid=strong_unpaid)
assert len(controls)==8
print(json.dumps(dict(native_world_histories=len(rows),actual_counterfactual_duty_dispatches=8*len(rows),
                      controls=controls),sort_keys=True))
