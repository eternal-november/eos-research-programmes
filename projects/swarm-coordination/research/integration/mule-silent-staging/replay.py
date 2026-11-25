from itertools import combinations_with_replacement, product
from model import Fault,Primary,envelope,trace

def direct(state,work,D):
    # Enumerate each allowed prefix staging policy on the same silent
    # observation. For the reaction phase, enumerate possible starts against
    # actual readiness, positive gate/quiet/grant cuts and the deadline.
    valid=[]
    for mask in range(1<<D):
        v=[0]
        for t in range(D):
            v.append(v[-1]+(mask>>t&1))
        if v[-1]>work:
            continue
        for f in state:
            after=f.notice+work-v[f.notice]
            if not any(s>=after and s>=f.notice and s>=f.gate and s>=f.quiet and s>=f.grant
                       and s+f.duration<=D for s in range(D+1)):
                break
        else:
            valid.append(v)
    return tuple(min(v[t] for v in valid) for t in range(D+1)) if valid else None

# Exhaustive two-recovery-outcome families. Readiness, exclusive authority,
# physical clearance and duration are coupled only through a common trace.
D=6
library=[Fault(t,g,q,2,d) for t,g,q,d in product((1,3,4),(1,4),(2,5),(1,3))]
comparisons=0
for a,b in combinations_with_replacement(library,2):
    for w in range(5):
        assert (e:=envelope((a,b),w,D))==direct((a,b),w,D),(a,b,w,e)
        if e is not None:
            for f in (a,b):
                got=trace(e,f,w,D)
                assert got[0]==max(f.notice+w-e[f.notice],f.notice,f.gate,f.quiet,f.grant)+f.duration
                assert got[0]<=D and got[2]==(1,3,5)
        comparisons+=1

work,D=4,8
faults=(Fault(2,3,4,3,3),Fault(4,5,4,5,3))
cal=envelope(faults,work,D)
assert cal==(0,0,1,2,3,3,3,3,3)
immediate=tuple(min(t,work) for t in range(D+1))
wait=(0,)*(D+1)
assert [trace(cal,f,work,D)[0] for f in faults]==[8,8]
assert [trace(wait,f,work,D)[0] for f in faults]==[None,None]
assert trace(cal,Primary(2),work,D)[:2]==(2,1)
assert trace(immediate,Primary(2),work,D)[:2]==(2,2)
assert [trace(cal,f,work,D)[1] for f in faults]==[1,3]
assert envelope((Fault(2,7,4,3,3),*faults),work,D) is None
assert envelope((Fault(4,5,6,5,3),*faults),work,D) is None
print(f"matched exact policy enumeration: {comparisons} two-outcome cases")
print(f"minimum cumulative silent staging: {cal}")
print("both second-fault histories finish at 8; waiting until notice misses 8")
print("primary settles at 2; minimum policy spends 1 prep tick, eager spends 2")
print("the independent inspection continues at ticks 1,3,5 in all traces")
print("later no-entry evidence or missing physical clearance can make deadline impossible")
