from itertools import product
from subprocess import run
from pathlib import Path
from collections import Counter
import sys
d=Path(sys.argv[1]).resolve()
c=list(product((3,4),(1,2),(1,2),(-1,0,20,100),(960,1000,1024,1025,1040),(0,1)))
# Preceding monitor input has to precede I's queued bit.
assert all(x[3]<x[4] for x in c)
inp=''.join(str(i)+' '+' '.join(map(str,case))+'\n' for i,case in enumerate(c))
rows=run([d/'addressed'],cwd=d,input=inp,capture_output=True,text=True,check=True).stdout.splitlines()
assert len(rows)==len(c)
n=Counter()
for i,txt in enumerate(rows):
    key,signal,old,mon=map(int,txt.split())
    assert i==key
    site,sender,receiver,prior,t0,roster=c[key]
    t=t0+64*roster
    enough=not (sender==1 and prior>=0 and t-prior<=1024)
    # The source receives the transmitter's configuration; comparing the
    # candidate limit only to Q's configuration is a deliberately false null.
    receiver_only=not (receiver==1 and prior>=0 and t-prior<=1024)
    assert signal==(t if enough else -1) and old==1 and mon==int(prior>=0)
    n['sender_receiver_model_disagrees']+=enough!=receiver_only
    n['values_received']+=enough
    n['in_time_ignoring_decode']+=enough and t<=1024
    n['still_queued_after_first_dispatch']+=roster

# Additional bounded clock abstraction: hardware phase is not measured.
# Updates repeat every period ticks with unknown integer phase. Relate the
# actual first eligible dispatch, reception budget and final decode deadline.
phase=0
for movement,own_setup,period,decode,allow_equal in product(
        (768,896,960,992,1000,1024),(0,8,32),(8,16,32,64,128),(0,8,16),(False,True)):
    t=movement+own_setup+int(not allow_equal)
    times=[t+((p-t)%period) for p in range(period)]
    for p,q in enumerate(times):
        expected=next(k for k in range(t,t+period) if k%period==p)
        assert q==expected
        phase+=1
    assert max(times)+decode==t+period-1+decode
    assert all(q+decode<=1024 for q in times)==(t+period-1+decode<=1024)
assert not (1024+1<=1024) # no slack at all after movement at the next choice
print(len(c),'native addressed branch-slot cases',dict(sorted(n.items())))
print(phase,'exact quantized clock phases')
