"""Independent exact arithmetic replay; imports no main benchmark code."""
from itertools import product
import json
from pathlib import Path

neighbors = ((1,2),(0,3),(0,3),(1,2))
worlds = [p for p in product(*[(-1,)+ns for ns in neighbors])
          if all(j == -1 or p[j] != i for i,j in enumerate(p))]
records=[]
for p in worlds:
    edge02 = p[2] == 0
    edge13 = p[3] == 1
    if edge02:
        final=(3,2,1)
    elif not edge13:
        final=(2,1,3)
    else:
        final=(2,3,1)
    sequence=(-1,-1,1,-1,0,0)+final+(-1,)
    prev=(0,)*4
    energy=0
    peak=0
    for t,a in enumerate(sequence):
        u=tuple(2 if i==a else 0 for i in range(4))
        load=tuple(u[i]+(prev[p[i]] if p[i]!=-1 else 0) for i in range(4))
        assert max(load)<=3,(p,t,sequence,load)
        assert sum(u)<=2
        energy+=sum(u)
        peak=max(peak,max(load))
        if t==3:
            assert (load[3]==2)==edge13
        if t==5:
            assert (load[2]==2)==edge02
        prev=u
    assert energy==12
    assert sequence[2]==1 and sequence[4]==0
    assert sequence[5]==0 and 2 in sequence[6:8]
    assert 1 in sequence[6:9] and 3 in sequence[6:9]
    records.append({'parents':p,'sequence':sequence,'energy':energy,'peak_twice_load':peak})
result={'world_count':len(worlds),'all_worlds_safe_and_complete':True,
        'diagnostic_pulses':0,'energy_per_world':12,'records':records}
out=Path(__file__).with_name('productive_evidence_witness_check.json')
out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='records'}))
