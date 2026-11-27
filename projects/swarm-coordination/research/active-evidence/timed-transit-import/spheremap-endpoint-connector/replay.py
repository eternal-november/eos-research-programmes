import itertools, json, math, pathlib, random, subprocess, sys
u=pathlib.Path(sys.argv[1])
assert 'max_graph_dist_for_spheremap_planning: 10' in (u/'params.yaml').read_text()
assert 'enforced_max_sphere_radius  = 3;' in (u/'spheremap.h').read_text()
service=(u/'mapper.cpp').read_text()
assert 'ros::Time(0)' in service and 'resp.success = true;' in service
assert 'path_comp_res.value()[0].positions.size() == 0' in service
witness=( ((12,12,0,3,1),(12,15,0,3,1)), (0,0,0),(12,15,0),10,0 )
cases=[witness,witness[:-1]+(1,)]
rng=random.Random(902813)
for k in range(4096):
    pts=tuple(tuple(rng.randrange(-17,18) for _ in range(3))+
             (rng.randrange(1,4),1) for _ in range(3))
    p=tuple(rng.randrange(-2,3) for _ in range(3))
    q=tuple(rng.randrange(-5,6) for _ in range(3))
    m=rng.randrange(2,12)
    cases.append((pts,p,q,m,k%2))
def flatten(xs): return ' '.join(str(a) for a in xs)
def query(item):
    nodes,p,q,m,mode=item
    return str(len(nodes))+' '+flatten(a for n in nodes for a in n)+' '+flatten((*p,*q,m,mode))
proc=subprocess.run([sys.argv[2]],input='\n'.join(map(query,cases))+'\n',text=True,
                    capture_output=True,check=True)
rows=proc.stdout.splitlines()
assert len(rows)==len(cases)
def ref(nodes,p,q,m):
    def opts(x):
        return sorted((math.dist(n[:3],x)-n[3],i) for i,n in enumerate(nodes)
           if max(abs(a-b) for a,b in zip(n[:3],x))<=m+3)
    a=opts(p); b=[v for v in opts(q) if v[0]<=m]
    return a,b,bool(a and b and math.dist(nodes[a[0][1]][:3],nodes[b[0][1]][:3])<
        nodes[a[0][1]][3]+nodes[b[0][1]][3])
for text,case in zip(rows,cases):
    nodes,p,q,m,mode=case
    start,margin,ngoal,r,*tail=map(float,text.split())
    a,b,w=ref(nodes,p,q,m)
    assert (start,ngoal,r)==(a[0][1] if a else -1,bool(b),w),(case,text)
    assert abs(margin-(a[0][0] if a else 0))<8e-6
    if w:
        assert tail==list(nodes[a[0][1]][:4]+nodes[b[0][1]][:4])
assert rows[0]==rows[1]
_,margin,*_=map(float,rows[0].split())
assert margin>10
# Fixed exact radii in both two-obstacle completions; only the named
# source connector has the extra obstacle. This is constructed geometry.
S=((12,12,-3),(12,15,-3))
extra=(4,4,0)
P=((12,12,0),(12,15,0))
for obs in (S,S+(extra,)):
    assert [min(math.dist(p,b) for b in obs) for p in P]==[3,3]
def segdist(a,b,x):
    v=[j-i for i,j in zip(a,b)]
    t=sum(i*(r-j) for i,r,j in zip(v,x,a))/sum(i*i for i in v)
    t=min(max(t,0),1)
    return math.dist([i+t*j for i,j in zip(a,v)],x)
safe=min(segdist((0,0,0),P[0],q) for q in S)
obstructed=min(segdist((0,0,0),P[0],q) for q in S+(extra,))
assert safe==3 and obstructed==0
# Exact transverse radius on the full segment between two equal balls.
# Eroding each ball individually loses configurations in the measured
# lens; neither checker supplies the separate missing endpoint connector.
r,a,b=10,6,6
assert a+b>=r and a*a+b*b<r*r
print(json.dumps(dict(native_cases=len(rows),same_native_response=rows[0],
     start_gap=round(margin,6),requested_bound=10,
     source_connector_clearance=[safe,obstructed],
     capsule_example={"radius":r,"half_separation":a,"robot_radius":b}),indent=2,sort_keys=True))
