from pathlib import Path
from subprocess import run
from tempfile import TemporaryDirectory
from hashlib import sha1
import struct,sys,re,heapq
d=Path(sys.argv[1]).resolve()
r=Path(__file__).resolve().parent
base=(d/'table.cc').read_bytes()
assert sha1(f'blob {len(base)}\0'.encode()+base).hexdigest()=='c52cf9cd00d221680d521bd70cdccbc64195881e'
b=(d/'cave.dat').read_bytes()
assert sha1(f'blob {len(b)}\0'.encode()+b).hexdigest()=='5d53ca3aefec299168a1b49f6d2900bf51b42774'
n,=struct.unpack_from('<Q',b)
assert n==1533365 and (len(b)-8)/20==n+18
f=b[8:8+20*n]
bmap={(x,y,z):u for x,y,z,u in struct.iter_unpack('<iiiQ',f)
      if 95<=x<=105 and 50<=y<=75 and 0<=z<=10}
adj={}
for a,b,w in re.findall(r'(\d+)\s*--\s*(\d+)\s*\[label=(\d+)\]',(d/'world.dot').read_text()):
    a,b,w=map(int,(a,b,w))
    adj.setdefault(a,[]).append((b,w));adj.setdefault(b,[]).append((a,w))
ids=[18,39,16,13,42,6]
def distance(a):
    ds={a:0};pq=[(0,a)]
    while pq:
        t,k=heapq.heappop(pq)
        if t!=ds[k]:continue
        for v,w in adj[k]:
            if t+w<ds.get(v,10**8):
                ds[v]=t+w;heapq.heappush(pq,(t+w,v))
    return [ds[i] for i in ids]
(d/'dist6.tsv').write_text('\n'.join(' '.join(map(str,distance(i))) for i in ids)+'\n')
c=base.decode()
i=c.index('bool VisibilityTable::LoadLUT()')
(d/'load.inc').write_text(c[i:c.index('\n}',i)+2])
shim=d/'visibility_shim.hpp'
s=shim.read_text()
assert 'std::string lutPath;' not in s
try:
    shim.write_text(s.replace('struct VisibilityTable{','struct VisibilityTable{\n std::string lutPath;\n bool LoadLUT();',1))
    (d/'actual.cpp').write_bytes((r/'actual.cpp').read_bytes())
    run(['g++','-std=c++17','-O2','-Wno-return-type','actual.cpp','-o','actual'],cwd=d,check=True)
    rows=run([d/'actual'],cwd=d,capture_output=True,text=True,check=True).stdout.splitlines()
finally:
    shim.write_text(s)
assert int(rows[0])==n
vals=[tuple(map(int,line.split())) for line in rows[1:-2]]
assert len(vals)==11*26*11
for x,y,z,label,ok in vals:
    assert label==bmap.get((x,y,z),-1)
    assert ok==(label in (13,42)) # both cost <=5 and within 72; other configured labels absent in this tube
print(n,'native LUT records loaded;',len(vals),'queried positions;',sum(v[4] for v in vals),'received addressed packets')
print(18,'trailing records outside declared native count')
print([(v[0:4],v[4]) for v in vals if v[0]==100 and v[1] in (58,62,63,75) and v[2] in (0,1,2)])

assert rows[-2:]==['courier 6, altitude 6: near relay required and report delivered','courier 42, altitude 8: direct report delivered']
print(*rows[-2:],sep='\n')
