import json
import subprocess
import sys
from itertools import product

names=('stock','snapshot','factorized','joint')
cases=[]
for cap in range(2,9):
    for a,b,shared,mask in product(range(1,cap+1),range(1,cap+1),range(2),range(1,16)):
        for w in range(4):
            if mask>>w&1:
                for k in range(4):
                    cases.append((cap,a,b,shared,mask,w,k))
proc=subprocess.run([sys.argv[1]],input=''.join(' '.join(map(str,c))+'\n' for c in cases),
                    text=True,check=True,capture_output=True)
lines=[r for r in proc.stdout.splitlines() if not r.startswith('Problem getting state')]
assert len(lines)==len(cases)
counts={k:dict(run=0,old_failed=0,early_peer=0,early_other=0) for k in names}
witness={}
benefit=0
clock=(3,3,4,5) # quarter-second units
for (cap,a,b,shared,mask,w,k),line in zip(cases,lines):
    worlds=[i for i in range(4) if mask>>i&1]
    if k==0:
        early=False
    elif k==1:
        early=all(not shared or t>4 or a+b<=cap for t in (clock[v] for v in worlds))
    elif k==2:
        early=all(not (shared or al) or t>4 or a+b<=cap
                  for (al,t) in product({i!=0 for i in worlds},{clock[i] for i in worlds}))
    else:
        # Strong direct schedule search: test both early and hold, explicitly
        # simulate each full history's debits instead of a marginal bound.
        good=[]
        for option in (False,True):
            all_ok=True
            for i in worlds:
                second=clock[i]
                old_dst='r1' if i else 'r0'
                bb=('p' if shared else 'q','r1',b,0 if option else second+5)
                aa=('p',old_dst,a,second)
                Q=sorted([aa,bb],key=lambda inst:inst[-1])
                tx={};rx={}
                for src,dst,size,now in Q:
                    used=lambda L,key:sum(d for t,d in L.get(key,[]) if t>=now-4)
                    if used(tx,src)+size>cap or used(rx,dst)+size>cap:
                        all_ok=False
                        break
                    tx.setdefault(src,[]).append((now,size))
                    rx.setdefault(dst,[]).append((now,size))
            if all_ok:good.append(option)
        assert good
        early=max(good)
    b0,c0,ap,bp,cp=map(int,line.split())
    old_ok=not early or not (shared or w!=0) or clock[w]>4 or a+b<=cap
    assert (b0,c0,ap,bp,cp)==(early,k!=0,old_ok,1,1)
    r=counts[names[k]]
    r['run']+=1;r['old_failed']+=not ap;r['early_peer']+=b0;r['early_other']+=c0
    if k==3 and early and a+b>cap and any((shared or j!=0) for j in worlds) \
            and any(clock[j]<=4 for j in worlds):
        benefit+=1
    if (cap,a,b,shared,mask,w) in [(5,3,3,0,9,3),(5,3,3,0,3,1),(5,3,3,0,5,2)]:
        witness.setdefault(str((mask,w)),{})[names[k]]=list(map(int,line.split()))
print(json.dumps(dict(counts=counts,strictly_more_early_peer_than_marginal=benefit,
    samples=witness),sort_keys=True))
