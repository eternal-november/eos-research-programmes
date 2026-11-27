from pathlib import Path
from itertools import product
from collections import defaultdict
import xml.etree.ElementTree as XML
import math,re,heapq,json,subprocess
p=Path(__file__).resolve().parent

def inputs():
    d=defaultdict(dict)
    for x,y,c in re.findall(r"(\d+)\s+--\s+(\d+)\s+\[label=(\d+)",(p/"world.dot").read_text()):
        x,y,c=map(int,(x,y,c))
        assert x!=y and y not in d[x]
        d[x][y]=d[y][x]=c
    xyz={}
    for include in XML.parse(p/"world.sdf").findall("./world/include"):
        s=include.findtext("name") or ""
        if re.fullmatch(r"tile_\d+",s):
            xyz[int(s[5:])]=tuple(map(float,include.findtext("pose").split()[:3]))
    across={}
    for x in d:
        best={x:0}; queue=[(0,x)]
        while queue:
            c,y=heapq.heappop(queue)
            if c!=best[y]:continue
            for z,w in d[y].items():
                if c+w<best.get(z,math.inf):
                    best[z]=c+w
                    heapq.heappush(queue,(c+w,z))
        across[x]=best
    # Decouple graph projection from source evaluation: check shortest paths
    # via a second graph recurrence over the complete imported map.
    n=len(d); order=sorted(d)
    f=[[0 if x==y else d[x].get(y,math.inf) for y in order] for x in order]
    for k in range(n):
        for i in range(n):
            if f[i][k]==math.inf:continue
            for j in range(n):
                f[i][j]=min(f[i][j],f[i][k]+f[k][j])
    assert all(f[i][j]==across[x].get(y,math.inf)
               for i,x in enumerate(order) for j,y in enumerate(order))
    return d,xyz,across

def main():
    g,x,best=inputs()
    cases=[]
    for r in sorted(g):
        for s in sorted(g[r]):
            for z in sorted(g[r]):
                if s>=z or not {s,r,z}<=x.keys(): continue
                actual=best[s][z]
                if not (actual>10>=max(best[s][r],best[r][z])):continue
                point=x[r]
                for axis in range(3):
                    signed=lambda sign:tuple(v+sign*(i==axis) for i,v in enumerate(point))
                    a,b=signed(-1),signed(1)
                    ra,rb=(max(math.dist(x[s],v),math.dist(x[z],v)) for v in (a,b))
                    # Avoid a numerically marginal claim; query below, between,
                    # and above the two distances, with no tie at a boundary.
                    if abs(ra-rb)<1e-3 or min(ra,rb)<2:continue
                    for way,cut in (("neither",min(ra,rb)-.1),("between",(ra+rb)/2),
                                    ("both",max(ra,rb)+.1)):
                        cases.append(([s,r,z],[[best[i][j] for j in (s,r,z)] for i in (s,r,z)],
                                      [x[s],x[z],a,b],cut,axis,way, ra<=cut,rb<=cut))
    assert cases
    count=len(cases)
    raw=[str(count)]
    for sites,dist,coords,cap,i,m,a,b in cases:
        raw.append(" ".join(str(v) for v in sites+[k for row in dist+coords for k in row]+[cap]))
    basic=subprocess.run([str(p/"first_insert")],input="\n".join(raw)+"\n",text=True,
                         check=True,capture_output=True).stdout.splitlines()
    modes={"a":(1,1,"a"),"b":(1,1,"b"),"ab":(2,2,"a"),
           "ba":(2,2,"b"),"batch":(1,2,"a"),"none":(0,0,None),
           "restore-ab":(3,2,"a"),"restore-ba":(3,2,"b")}
    assert len(basic)==len(cases)*len(modes)
    witnesses=[]
    for j,(sites,dist,coords,cap,axis,way,a,b) in enumerate(cases):
        records=[]
        for k,(name,(updates,holders,first)) in enumerate(modes.items()):
            r=basic[j*len(modes)+k].split()
            r=[*map(int,r[:3]),r[3],*map(int,r[4:])]
            ok=a if first=="a" else b if first else False
            cost=max(dist[0][1],dist[1][2]) if first else dist[0][2]
            exp=[*sites,name,updates,holders,cost,int(first is not None),ord(first or "\0"),int(ok),int(first is not None),int(ok),2*int(ok),1]
            assert r==exp,(coords,way,r,exp)
            records.append(r)
        if way=="between":
            assert a!=b and records[2][5]==records[3][5]==2
            assert records[2][-3]!=records[3][-3]
            witnesses.append({"tiles":sites,"costs":[dist[0][2],dist[0][1],dist[1][2]],
                              "centres_and_samples":coords,"range":round(cap,8),
                              "axis":axis,"a_first_receives":a})
    print(json.dumps({"trials":len(basic),"imported_graph_tiles":len(g),
                      "opposite_outcome_witnesses":len(witnesses),"first":witnesses[0]},
                     sort_keys=True))
if __name__=="__main__":main()
