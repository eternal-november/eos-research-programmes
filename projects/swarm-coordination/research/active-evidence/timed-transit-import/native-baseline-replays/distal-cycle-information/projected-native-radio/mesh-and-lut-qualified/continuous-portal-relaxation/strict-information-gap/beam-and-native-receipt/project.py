"""Project all 20 distal tile-centre reference poses through the full RF graph."""
from pathlib import Path
from xml.etree import ElementTree as XML
from heapq import heappop,heappush
import re,json,sys,struct
S=(103,118,117,104,105,107)
P=Path(".")
G={}
for u,v,w in re.findall(r'(\d+)\s*--\s*(\d+)\s*\[label=(\d+)\]',(P/"world.dot").read_text()):
    u,v,w=int(u),int(v),int(w)
    G.setdefault(u,[]).append((v,w));G.setdefault(v,[]).append((u,w))
assert len(G)==158
pos={}
for e in XML.parse(P/"world.sdf").findall(".//include"):
    k=e.findtext("name")
    if k and k.startswith("tile_"):
        pos[int(k[5:])]=list(map(int,e.findtext("pose").split()[:3]))
assert len(pos)==157
survey=json.loads(Path(sys.argv[1]).read_text())
assert survey["triangles"]==304228
pose_vertices={}
for i in S:
    v=survey["sites"][str(i)]
    if v["shifted_box"]:
        center=v["shifted_box"][0][0]
        assert v["shifted_box"][0][3]>0
    else:
        center=[*v["origin"][:2],v["bracketed_box"][0][0]]
        assert v["bracketed_box"][0][3]>0
    if i in (118,117):
        ray=json.loads(Path(sys.argv[3]).read_text())
        center=ray["A" if i==118 else "B"]["observer"]
    pose_vertices[tuple(center)]=i
# Decode exactly the native LoadLUT record count, rather than reading
# trailing bytes. Last assignment wins if a coordinate repeats.
b=Path(sys.argv[2]).read_bytes()
N=struct.unpack_from("<Q",b)[0]
end=8+20*N
assert (N,len(b)-end)==(1533365,360)
membership={}
for x,y,z,v in struct.iter_unpack("<iiiQ",memoryview(b)[8:end]):
    key=(x,y,z)
    if key in pose_vertices:membership[key]=v
assert membership==pose_vertices
for xyz,v in membership.items():pos[v]=list(xyz)
print("LUT-qualified padded mesh-clear sites",len(membership))
print("stacked-pose chord intersects tested collision mesh",bool(survey["chord_collision_vertex"]))
def shortest(u):
    best={u:0};OPEN=[(0,u)]
    while OPEN:
        d,v=heappop(OPEN)
        if d!=best[v]:continue
        for k,w in G[v]:
            if d+w<best.get(k,10**6):
                best[k]=d+w;heappush(OPEN,(d+w,k))
    assert len(best)==158
    return best
a=shortest(103)
assert (a[118],a[117])==(18,10)
with (P/"sites.tsv").open("w") as f:
    for u in S:print(u,*pos[u],file=f)
    for u in S:
        D=shortest(u);print(*(D[v] for v in S),file=f)
    for state in ray["beam_codes"]:print(*state,file=f)
