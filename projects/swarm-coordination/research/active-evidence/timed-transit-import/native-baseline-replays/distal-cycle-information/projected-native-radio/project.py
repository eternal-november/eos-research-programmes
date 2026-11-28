"""Project all 20 distal tile-centre reference poses through the full RF graph."""
from pathlib import Path
from xml.etree import ElementTree as XML
from heapq import heappop,heappush
import re
S=(103,118,117,104,105,106,107,108,114,115,116,119,121,122,124,128,130,132,156,157)
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
