from pathlib import Path
from subprocess import run
from tempfile import TemporaryDirectory
from hashlib import sha1
import struct,sys,re,heapq
d=Path(sys.argv[1]).resolve()
r=Path(__file__).resolve().parent
sys.path.insert(0,str(r.parent.parent))
from timeline import BRANCH,load,duration
from decimal import Decimal as D
first=[(100,100,6),(101,83,6),(102,82,7),(102,75,8),(100,75,8)]
def travel(a,b):
    length=sum(D(u-v)**2 for u,v in zip(a,b)).sqrt()
    return 2*length.sqrt() if length<=9 else length/3+3
arrival=sum(travel(a,b) for a,b in zip(first,first[1:]))
assert D('19.45')<arrival<D('19.46')
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

def position(path,s,when):
    for p,q in zip(path,path[1:]):
        t=duration([p,q]);end=s+t
        if when<=end:
            L=sum(abs(a-b) for a,b in zip(p,q))
            peak=min(D(3),D(L).sqrt())
            t0=peak;t1=t-peak;h=when-s
            assert 0<=h<=t
            x=h*h/2 if h<=t0 else (D(L)-(t-h)**2/2 if h>=t1 else peak*h-peak**2/2)
            return [D(a)+(D(b-a)/L)*x for a,b in zip(p,q)]
        s=end
    return path[-1]
installer=load('installer')
installer=installer[:-2]+[(0,3,installer[-3][2]),(0,3,6)]
payload=[]
for arm in ('near','far'):
    t=arrival
    for omit in range(3):
        ix=position(installer,D(14),t+(D('.25') if omit==2 else D('.125')))
        ax=position(installer,D(14),t+D('.375'))
        payload.append(' '.join(map(str,(int(arm=='near'),omit,t,*ix,*ax))))
try:
    shim.write_text(s.replace('struct VisibilityTable{','struct VisibilityTable{\n std::string lutPath;\n bool LoadLUT();',1))
    (d/'actual.cpp').write_bytes((r/'joint.cpp').read_bytes())
    run(['g++','-std=c++17','-O2','-Wno-return-type','actual.cpp','-o','actual'],cwd=d,check=True)
    rows=run([d/'actual'],input='\n'.join(payload)+'\n',cwd=d,capture_output=True,text=True,check=True).stdout.splitlines()
finally:
    shim.write_text(s)
assert rows==[f'{arm} {fault} old, old receipt, addressed gate read, {site}, new and new receipt checked'
              for arm,site in [('near','no relay'),('far','no relay')] for fault in range(3)]
print(*rows,sep='\n')
