"""Build the induced RF projection on certified stops and fixed actors."""
from pathlib import Path
from heapq import heappop,heappush
from fractions import Fraction as F
import re,struct,json,sys

files=list(map(Path,sys.argv[1:]))
paths,rays,sites=[json.loads(p.read_text()) for p in files[:3]]
fixed=[tuple(p) for p in [sites['103'],rays['A']['observer'],rays['B']['observer'],
                       sites['104'],sites['105'],sites['107']]]
def intersects(s,t,p,r):
    lo,hi=F(0),F(1)
    for a,b,c in zip(s,t,p):
        if a==b:
            if abs(a-c)>r:return False
        else:
            u,v=sorted((F(c-a-r,b-a),F(c-a+r,b-a)))
            lo,hi=max(lo,u),min(hi,v)
    return lo<=hi
for path in paths.values():
    arr=path['polyline']
    for u,v in zip(arr,arr[1:]):
        assert all(not intersects(u,v,p,F(604,1000)) for p in fixed[1:]), (u,v)
coords=list(dict.fromkeys(fixed+[tuple(p) for q in paths.values() for p in q['polyline']]))
lut={}
b=files[3].read_bytes()
nr,=struct.unpack_from('<Q',b)
coords_set=set(coords)
for x,y,z,k in struct.iter_unpack('<iiiQ',memoryview(b)[8:8+20*nr]):
    if (x,y,z) in coords_set:lut[x,y,z]=k
assert set(lut)==coords_set
assert [lut[p] for p in fixed]==[103,118,117,104,105,107]
g={}
for a,b,w in re.findall(r'(\d+)\s*--\s*(\d+)\s*\[label=(\d+)\]',files[4].read_text()):
    a,b,w=map(int,(a,b,w))
    g.setdefault(a,[]).append((b,w));g.setdefault(b,[]).append((a,w))
assert len(g)==158
def shortest(s):
    best={s:0};q=[(0,s)]
    while q:
        d,u=heappop(q)
        if best[u]!=d:continue
        for v,w in g[u]:
            if d+w<best.get(v,10**6):
                best[v]=d+w;heappush(q,(d+w,v))
    return best
D={i:shortest(i) for i in set(lut.values())}
with files[5].open('w') as o:
    print(len(coords),file=o)
    for p in coords:print(lut[p],*p,file=o)
    for p in coords: print(*(D[lut[p]][lut[q]] for q in coords),file=o)
    for row in rays['beam_codes']:print(*row,file=o)
    for name in 'AB':
        seq=[coords.index(tuple(p)) for p in paths[name]['polyline']]
        print(len(seq),*seq,file=o)
