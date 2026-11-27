import itertools, json, pathlib, subprocess, sys
from xml.etree import ElementTree as ET
source=pathlib.Path(sys.argv[1])
world=ET.fromstring((source/'world.sdf').read_bytes()).find('world')
obstacles={}
for m in world.findall('model'):
    name=m.get('name')
    if not name.startswith('performer_detector_rockfall_'): continue
    for pl in m.findall('plugin'):
        output=pl.find('output')
        if output is None or 'triggered-publisher' not in pl.get('filename',''):continue
        fields={match.get('field'):match.text for match in pl.findall('input/match')}
        assert len(pl.findall('input/match'))==2
        vals=[s for s in fields.values() if 'key: "state"' in s]
        assert len(vals)==1
        import re
        mode=int(re.search(r'value:\s*"([01])"',vals[0])[1])
        target=output.get('topic').split('/')[2]
        obstacles[target]=mode
assert [obstacles[f'dynamic_rocks_{i}'] for i in (1,2,3,4)]==[0,0,1,1]
tests=[
    ("outside",[(12,0),(12,0)],""),
    ("entry_dwell",[(12,0),(12,1),(12,1)],"1"),
    ("entry_exit",[(12,1),(12,0)],"10"),
    ("separate_actors",[(12,1),(30,1),(12,0),(30,1),(30,0)],"1100"),
]
def detector_ref(xs):
    S=set(); out=[]
    for i,v in xs:
        if (i in S)!=bool(v):out.append(str(v))
        if v:S.add(i)
        else:S.discard(i)
    return ''.join(out)
n_detector=len(tests)
for bits in itertools.product(range(2),repeat=6):
    for a in ((12,12,12,12,12,12),(12,30,12,30,12,30),(12,12,30,30,12,30)):
        xs=list(zip(a,bits));tests.append((None,xs,detector_ref(xs)))
logs=[
 ("same_second_one",5,[(1,1)]),
 ("same_second_two",5,[(1,2)]),
 ("fire_at_zero",1,[(0,1)]),
 ("exhausted_labels_as_fall",5,[(1,5),(2,1)]),
 ("same_second_then_repeated_exhaustion",5,[(1,5),(2,1),(3,1),(4,1)]),
 ("ordinary_single",1,[(1,1),(2,1)])
]
n_logs=len(logs)
for cap,names in itertools.product(range(1,7),itertools.product(range(4),repeat=4)):
    for secs in ((0,1,2,3),(1,1,1,2),(3,4,4,4)):
        logs.append((None,cap,list(zip(secs,names))))
def log_ref(cap,trace):
    last=0; zero=0; left=cap; events=[]
    total=0; broadcast=0
    for t,k in trace:
        for _ in range(k):
            if left>0:
                left-=1;total+=1
            if t==last: continue
            if left>0:
                events.append('rock_fall');broadcast+=1
            else:
                if zero==0:
                    events.append('rock_fall');broadcast+=1
                if zero==1:events.append('max_rock_falls')
                zero+=1
            last=t
    return total,left,broadcast,events
input_rows=['detect '+str(len(xs))+' '+' '.join(f'{a} {b}' for a,b in xs)
       for _,xs,_ in tests]
input_rows += ['log '+f'{cap} {len(seq)} '+' '.join(f'{a} {b}' for a,b in seq)
               for _,cap,seq in logs]
o=subprocess.run([sys.argv[2]],input='\n'.join(input_rows)+'\n',text=True,
    capture_output=True,check=True).stdout.splitlines()
assert len(o)==len(input_rows)
for (_,xs,v),got in zip(tests,o):assert got==v,(xs,v,got)
named={}
for (tag,cap,seq),got in zip(logs,o[len(tests):]):
    parts=got.split(maxsplit=3)
    spawns,left,count=map(int,parts[:3])
    wave=parts[3].rstrip(',').split(',') if len(parts)>3 else []
    assert (spawns,left,count,wave)==log_ref(cap,seq),(cap,seq,got)
    if tag:named[tag]={'case':seq,'spawns':spawns,'remaining':left,'broadcast':count,'logged':wave}
assert named['same_second_one']['logged']==named['same_second_two']['logged']==['rock_fall']
assert named['same_second_one']['remaining']!=named['same_second_two']['remaining']
assert named['fire_at_zero']['spawns']==1 and named['fire_at_zero']['logged']==[]
assert named['exhausted_labels_as_fall']['logged']==['rock_fall','rock_fall']
print(json.dumps(dict(detector_comparisons=len(tests)-n_detector,
    detector_named={k:v for k,_,v in tests[:n_detector]}, world_triggers=obstacles,
    logger_comparisons=len(logs)-n_logs, witnessed=named),indent=2,sort_keys=True))
