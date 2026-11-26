from itertools import product
import subprocess,sys,json
params=[p for p in product((0,1,2),(0,1),(0,1),(0,1),(0,1))
        if (p[3] or p[4]) and (p[0]==0 or not p[2])]
native=subprocess.run([sys.argv[1]],input=''.join(' '.join(map(str,p))+'\n' for p in params),
                      text=True,check=True,stdout=subprocess.PIPE)
out=[]
for case,line in zip(params,native.stdout.splitlines(),strict=True):
    phase,cancel,late,s,r=case
    first,gone,changed,a,b,n,u,default=map(int,line.split())
    # Independent policy tree with old priority, conditional release and the
    # two physical ledgers. An already attempted send cannot be undone.
    source_feasible=(phase==0 and late) or (phase==2 and not s)
    can_drop=phase==0 and cancel and not source_feasible
    expected=source_feasible or can_drop
    assert first==int(source_feasible)
    assert gone==int(can_drop) and changed==b==int(expected)
    assert a==u==1 and default==int(not expected)
    assert n==int(phase!=2 and not can_drop)
    out.append(dict(case=case,first_rebind=first,optional_cancelled=gone,accepted=changed,
                    old_first=a,old_tail=b,optional_arrival=n,independent=u,
                    original_physical_path_unavailable=default))
assert len(out)==24
print(json.dumps(out,sort_keys=True,indent=2))
