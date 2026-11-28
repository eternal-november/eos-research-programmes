"""Derive projected graph distances and confirm positions from pinned Cave sources."""
from pathlib import Path
import heapq
import re
from xml.etree import ElementTree as XML
ids=(18,39,16,13,42)
g={}
for u,v,w in re.findall(r'(\d+)\s*--\s*(\d+)\s*\[label=(\d+)\]', Path("world.dot").read_text()):
    u,v,w=map(int,(u,v,w))
    g.setdefault(u,[]).append((v,w));g.setdefault(v,[]).append((u,w))
assert len(g)==158 and sum(map(len,g.values()))==326
points={int(i.attrib["name"].split("_")[1]):tuple(map(float,i.findtext("pose").split()[:3]))
        for i in XML.parse("world.sdf").findall(".//include")
        if re.fullmatch(r'tile_\d+',i.attrib.get("name",i.findtext("name",""))) and "name" in i.attrib}
if not points:
    points={int(i.findtext("name").split("_")[1]):tuple(map(float,i.findtext("pose").split()[:3]))
            for i in XML.parse("world.sdf").findall(".//include")
            if re.fullmatch(r'tile_\d+',i.findtext("name",""))}
# Selection uses specified sample points, not necessarily model origins.
assert all(u in points for u in ids)
def dijkstra(src):
    d={src:0}; todo=[(0,src)]
    while todo:
        d0,u=heapq.heappop(todo)
        if d0!=d[u]:continue
        for v,w in g[u]:
            if d0+w<d.get(v,float("inf")):
                d[v]=d0+w
                heapq.heappush(todo,(d[v],v))
    return [d[v] for v in ids]
matrix=[dijkstra(u) for u in ids]
assert matrix==[[0,10,11,7,8],[10,0,13,9,10],[11,13,0,4,3],[7,9,4,0,1],[8,10,3,1,0]]
Path("distances.tsv").write_text(''.join('\t'.join(map(str,r))+'\n' for r in matrix))
