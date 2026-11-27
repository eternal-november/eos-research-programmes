"""Pinned .dot and Gazebo fixture exercise for effective RF model selection."""
import heapq, json, math, pathlib, re, struct, subprocess, sys, tempfile
from xml.etree import ElementTree as ET
R=pathlib.Path(sys.argv[1])
B=sys.argv[2]
dot=(R/'world.dot').read_text()
g={int(x):{} for x in re.findall(r'^\s*(\d+)\s+\[label="\d+::[^"]+"\];',dot,re.M)}
for a,b,c in (map(int,m) for m in re.findall(r'(\d+)\s+--\s+(\d+)\s+\[label=(\d+)\];',dot)):
    assert b not in g[a] and a not in g[b]
    g[a][b]=g[b][a]=c
def shortest(a):
    d={a:0}; queue=[(0,a)]
    while queue:
        cost,u=heapq.heappop(queue)
        if d[u]!=cost: continue
        for v,w in g[u].items():
            n=cost+w
            if n<d.get(v,math.inf):
                d[v]=n;heapq.heappush(queue,(n,v))
    return d
costs={a:shortest(a) for a in g}
world=ET.fromstring((R/'world.sdf').read_bytes()).find('world')
def rounded(p):
    return tuple(int(math.copysign(math.floor(abs(x)+.5),x)) for x in p)
xyz={}; samples={}
for elem in world.findall('include'):
    name=elem.findtext('name','')
    if re.fullmatch(r'tile_\d+',name) or name=='base_station':
        a=0 if name=='base_station' else int(name.split('_')[1])
        if a not in g: continue
        p=tuple(map(float,elem.findtext('pose').split()[:3]))
        assert a not in xyz
        xyz[a]=p
        s=rounded(p)
        samples[s]=a if s not in samples else None
samples={s:a for s,a in samples.items() if a is not None}
xyz={a:xyz[a] for a in sorted(samples.values())}
ign=(R/'launch.ign').read_text()
for expected in [
    '<comms_model_type>visibility_range</comms_model_type>','<max_range>500.0</max_range>',
    '<comms_cost_max>10</comms_cost_max>','<visibility_cost_to_fading_exponent>0.2</visibility_cost_to_fading_exponent>',
    '<sigma>10.0</sigma>','<L0>40</L0>','$commsFadingExponent = 1.5']:
    assert expected in ign

# One staged relay route built from actual graph edges. It is not read
# from stock Gazebo, and selected route computation is not replayed.
pred={0:None}; queue=[0]
for a in queue:
    for b in sorted(g[a]):
        if b in xyz and b not in pred and g[a][b]<=10 and math.dist(xyz[a],xyz[b])<500:
            pred[b]=a;queue.append(b)
end=min((a for a in queue if math.dist(xyz[0],xyz[a])>500),
        key=lambda a:(math.dist(xyz[0],xyz[a]),a))
path=[end]
while path[-1]!=0: path.append(pred[path[-1]])
path.reverse()
hops=list(zip(path,path[1:]))
relay_count=len(path)-2
relay_weight=max(costs[a][b] for a,b in hops)
relay_spans=[math.dist(xyz[a],xyz[b]) for a,b in hops]
direct_range=math.dist(xyz[0],xyz[end])
assert relay_count>=1 and relay_weight<=10 and max(relay_spans)<500<direct_range

queries=[(a,b,xyz[a],xyz[b]) for a in xyz for b in xyz if a!=b]
for q in ((-100.,0.,0.),(-600.,0.,0.)):
    assert rounded(q) not in samples
    queries.append((0,None,xyz[0],q))
weights=[[a,b,c] for a,m in costs.items() for b,c in m.items()]
request=[[len(weights)]]+weights+[[0,*p,*q] for _,_,p,q in queries]
request.append([relay_count,*xyz[0],*xyz[end],0,end,relay_weight,
    max(relay_spans[1:-1],default=0),*xyz[path[1]],*xyz[path[-2]]])
with tempfile.TemporaryDirectory() as work:
    present=pathlib.Path(work)/'staged.dat'
    absent=pathlib.Path(work)/'unset.dat'
    with present.open('wb') as s:
        s.write(struct.pack('=Q',len(samples)))
        for (x,y,z),a in samples.items():s.write(struct.pack('=iiiQ',x,y,z,a))
    out=subprocess.run([B,str(present),str(absent)],check=True,text=True,capture_output=True,
                       input=''.join(' '.join(map(str,line))+'\n' for line in request))
    assert str(absent) in out.stderr
mode,*results=out.stdout.splitlines()
assert mode=='visibility_range log_normal_range'
assert len(results)==len(queries)+1
counts={'both_finite':0,'range_only_finite':0,'neither_finite':0}
base={}; unmapped=[]
for (a,b,p,q),line in zip(queries,results):
    v,r,via,no,yes=map(float,line.split())
    d=math.dist(p,q)
    c=costs[a].get(b,math.inf)
    assert d>0
    def power(exponent):return -20-10*exponent*math.log10(d) if d<=500 else -math.inf
    assert math.isclose(v,power(1.5+.2*c) if c<=10 else -math.inf,rel_tol=1e-12)
    assert math.isclose(r,power(1.5),rel_tol=1e-12)
    assert (via,no,yes)==(0,0,1)
    tag='both_finite' if math.isfinite(v) else 'range_only_finite' if math.isfinite(r) else 'neither_finite'
    counts[tag]+=1
    if b is not None and a==0 and tag!='neither_finite':
        candidate=(d,b,c,v,r)
        if tag not in base or candidate<base[tag]:base[tag]=candidate
    if b is None: unmapped.append({'distance':d,'visibility_mean':str(round(v,6)),
                                    'range_mean':str(round(r,6))})
assert set(base)=={'both_finite','range_only_finite'}
v,r,via,no,yes=map(float,results[-1].split())
assert (r,via,no,yes)==(-math.inf,1,0,1)
assert math.isclose(v,-20-10*(1.5+.2*relay_weight)*
                    math.log10(max(relay_spans)+relay_count*2),rel_tol=1e-12)
print(json.dumps(dict(mode=mode,checks=len(queries),models=counts,samples=len(samples),
    conditional_route=dict(target=end,relays=relay_count,distance=round(direct_range,6),
                         largest_hop=round(max(relay_spans),6),cost=relay_weight,
                         visibility_mean=round(v,6),range_mean=str(r),tile_path=path),
    unmapped=unmapped,minimum_base_pair={
        tag:dict(tile=b,dist=round(d,6),cost=None if not math.isfinite(c) else c,
                 visibility_mean=str(round(v,6)),range_mean=str(round(r,6)))
        for tag,(d,b,c,v,r) in base.items()}),indent=2,sort_keys=True))
