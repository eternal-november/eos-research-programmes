from pathlib import Path
from hashlib import sha256
from xml.etree.ElementTree import parse
import numpy as np
from decimal import Decimal
P=Path(__file__).resolve().parent
def verify():
    for row in (P/'PINS.txt').read_text().splitlines():
        n,sha=row.split()
        assert sha256((P/n).read_bytes()).hexdigest()==sha,n
GRID=10**14
def collada(path,scale):
    r=parse(path).getroot()
    for p in r.iter():p.tag=p.tag.split('}')[-1]
    assert r.findtext('asset/up_axis')=='Z_UP'
    unit=float(r.find('asset/unit').attrib['meter'])
    assert unit==0.01
    nodes=r.findall('library_visual_scenes/visual_scene/node')
    g={e.attrib['id']:e for e in r.findall('library_geometries/geometry')}
    out=[]
    for node in nodes:
        assert [float(v) for v in node.findtext('matrix').split()]==list(np.eye(4).ravel())
        m=g[node.find('instance_geometry').attrib['url'][1:]].find('mesh')
        sources={e.attrib['id']:e for e in m.findall('source')}
        vertices=m.find('vertices')
        assert sum(v.get('semantic')=='POSITION' for v in vertices)==1
        pos=sources[next(v for v in vertices if v.get('semantic')=='POSITION').get('source')[1:]]
        assert pos.find('technique_common/accessor').get('stride')=='3'
        points=[]
        for j,word in enumerate(pos.findtext('float_array').split()):
            x=Decimal(word)*Decimal('0.01')*GRID*scale[j%3]
            assert x==x.to_integral_value()
            points.append(int(x))
        points=np.asarray(points,dtype=np.int64).reshape(-1,3)
        ts=m.findall('triangles')
        assert len(ts)==1
        inputs=ts[0].findall('input')
        stride=1+max(int(x.get('offset')) for x in inputs)
        vert=next(x for x in inputs if x.get('semantic')=='VERTEX')
        assert vert.get('source')[1:]==vertices.attrib['id']
        ix=np.fromstring(ts[0].findtext('p'),sep=' ',dtype=int).reshape(-1,stride)[:,int(vert.get('offset'))]
        tri=points[ix.reshape(-1,3)]
        assert len(tri)==int(ts[0].get('count'))
        out.append(tri)
    assert len(out)==len(g)==(4 if path.stem=='start' else 3)
    return np.concatenate(out)
def exact_separators(T,L,H):
    # Search a separator in floating arithmetic, then verify the integer
    # coefficients against the original decimal vertices and expanded box.
    X=np.asarray(T,dtype=float)/GRID
    lo=np.asarray(L,dtype=float)/GRID;hi=np.asarray(H,dtype=float)/GRID
    center=(lo+hi)/2;hh=(hi-lo)/2
    U=X-center
    ident=np.eye(3)
    e=np.roll(U,-1,axis=1)-U
    axes=np.concatenate((np.broadcast_to(ident,(len(T),3,3)),
                         np.cross(e[:,0,:],e[:,1,:])[:,None,:],
                         np.cross(e[:,:,None,:],ident[None,None,:,:]).reshape(-1,9,3)),axis=1)
    normas=np.linalg.norm(axes,axis=2)
    p=np.einsum('nvc,nac->nav',U,axes)
    R=np.abs(axes)@hh
    delta=np.maximum(p.min(axis=2)-R,-p.max(axis=2)-R)
    sep=np.divide(delta,normas,out=np.full_like(delta,-np.inf),where=normas>1e-13)
    index=sep.argmax(axis=1)
    samples=axes[np.arange(len(T)),index,:]
    samples=samples/np.linalg.norm(samples,axis=1)[:,None]
    axesI=np.rint(samples*10**6).astype(int).tolist()
    L,H=list(map(int,L)),list(map(int,H))
    margins=[]
    for row,c in zip(T.tolist(),axesI):
        assert any(c)
        bb0=sum(u*(a if u>=0 else b) for u,a,b in zip(c,L,H))
        bb1=sum(u*(b if u>=0 else a) for u,a,b in zip(c,L,H))
        projections=[sum(u*v for u,v in zip(c,q)) for q in row]
        p0,p1=min(projections),max(projections)
        separated=max(p0-bb1,bb0-p1)
        assert separated>0
        # Also provide a strict coordinate-invariant lower bound: normalized
        # Euclidean gap is at least divided through the L1 norm.
        margins.append(separated/(GRID*sum(map(abs,c))))
    return min(margins)


def visual_margin(T,lo,hi):
    # Numeric search/ranking only; selected signs are checked separately.
    lo=np.asarray(lo);hi=np.asarray(hi)
    center=(lo+hi)/2;hh=(hi-lo)/2
    U=T-center
    ident=np.eye(3)
    e=np.roll(U,-1,axis=1)-U
    axes=np.concatenate((np.broadcast_to(ident,(len(T),3,3)),
                         np.cross(e[:,0,:],e[:,1,:])[:,None,:],
                         np.cross(e[:,:,None,:],ident[None,None,:,:]).reshape(-1,9,3)),axis=1)
    norms=np.linalg.norm(axes,axis=2)
    p=np.einsum('nvc,nac->nav',U,axes)
    R=np.abs(axes)@hh
    delta=np.maximum(p.min(axis=2)-R,-p.max(axis=2)-R)
    sep=np.divide(delta,norms,out=np.full_like(delta,-np.inf),where=norms>1e-13)
    return sep.max(axis=1).min()


MODELS={0:'start',1:'tee',2:'corner',3:'corner2',4:'straight2',6:'corner',
        8:'straight3',9:'corner2',13:'straight',16:'tee',39:'tee',42:'straight',43:'straight'}
HEAD={
 'tee_lights.sdf':'Cave 3 Way 01 Type B','corner_lights.sdf':'Cave Corner 01 Type B',
 'corner2l.sdf':'Cave Corner 02 Type B','straight2l.sdf':'Cave Straight 02 Type B',
 'lights.sdf':'Cave Straight 05 Type B'}
def load_scene():
    d={v.findtext('name'):v for v in parse(P/'world.sdf').findall('.//include')}
    positions={0:tuple(map(Decimal,d['staging_area'].findtext('pose').split()))}
    positions.update({i:tuple(map(Decimal,d[f'tile_{i}'].findtext('pose').split())) for i in MODELS if i})
    geo={};fences=[]
    for filename,name in HEAD.items():
        n=parse(P/filename)
        assert n.findtext('.//include/uri').endswith(name)
        assert n.findtext('.//include/pose') in (None,'0 0 0 0 0 0')
        assert not n.findall('.//collision')
    for name in set(MODELS.values()):
        g=parse(P/(name+'.sdf'))
        cols=[(link,k) for link in g.findall('.//link') for k in link.findall('collision')]
        assert len(cols)==(5 if name=='start' else 1)
        for link,k in cols:
            if k.find('geometry/box') is not None:
                lp=tuple(map(Decimal,link.findtext('pose').split()))
                cp=tuple(map(Decimal,k.findtext('pose').split()))
                assert lp[3:]==cp[3:]==(0,0,0)
                size=tuple(map(Decimal,k.findtext('geometry/box/size').split()))
                lo=tuple(lp[i]+cp[i]-size[i]/2 for i in range(3))
                hi=tuple(lp[i]+cp[i]+size[i]/2 for i in range(3))
                fences.append((lo,hi));continue
            assert k.findtext('pose')=='0 0 0 0 0 0'
            lp=tuple(map(Decimal,link.findtext('pose','0 0 0 0 0 0').split()))
            assert lp[:5]==(0,0,0,0,0)
            assert lp[-1]==(Decimal('1.5708') if name=='start' else 0)
            sc=tuple(map(Decimal,k.findtext('geometry/mesh/scale').split()))
            geo[name]=(collada(P/(name+'.dae'),sc),lp[-1])
    def rot(t,q):
        k=q%4
        if k==0:return t
        if k==1:return t[:,:,[1,0,2]]*[-1,1,1]
        if k==2:return t*[-1,-1,1]
        return t[:,:,[1,0,2]]*[1,-1,1]
    mesh=[]
    for i,src in MODELS.items():
        x,y,z,a,b,theta=positions[i]
        assert a==b==0
        t,l=geo[src]
        total=float(theta+l)
        q=round(total/(np.pi/2))
        # two rotations max, decimal room conservative. Both planar L1
        # and collision shape transformations checked below.
        assert abs(total-q*np.pi/2)<0.000004
        assert int(np.abs(t[:,:,:2]).sum(axis=2).max())<110*GRID
        mesh.append(rot(t,q)+[int(w*GRID) for w in (x,y,z)])
    return np.concatenate(mesh),fences,{k:tuple(map(int,v[:3])) for k,v in positions.items()}

class Map:
    def __init__(self,T,fences):
        from collections import defaultdict
        self.T=T;self.fences=fences
        self.F=T.astype(float)/GRID
        self.lo=self.F.min(axis=1);self.hi=self.F.max(axis=1)
        self.cells=defaultdict(list)
        for i,(l,h) in enumerate(zip(self.lo,self.hi)):
            for a in range(int(np.floor(l[0]/4)),int(np.floor(h[0]/4))+1):
              for b in range(int(np.floor(l[1]/4)),int(np.floor(h[1]/4))+1):
                self.cells[a,b].append(i)
        from functools import lru_cache
        self.clear=lru_cache(None)(self.clear)
    def sub(self,l,h):
        ids=set()
        for i in range(int(np.floor(l[0]/4)),int(np.floor(h[0]/4))+1):
            for j in range(int(np.floor(l[1]/4)),int(np.floor(h[1]/4))+1):
                ids.update(self.cells[i,j])
        q=np.fromiter(ids,int)
        return q[np.logical_and(self.hi[q]>=l,self.lo[q]<=h).all(axis=1)]
    def clear(self,u,v):
        l=np.minimum(u,v)-.3005
        h=np.maximum(u,v)+.3005
        for a,b in self.fences:
            if all(float(a[i])<=h[i] and float(b[i])>=l[i] for i in range(3)):
                return False
        m=self.sub(l,h)
        return len(m)==0 or visual_margin(self.F[m],l,h)>1e-8
    def certificate(self,u,v,inflate=Decimal('.3005')):
        L=[int((Decimal(min(str(a),str(b),key=Decimal))-inflate)*GRID) for a,b in zip(u,v)]
        H=[int((Decimal(max(str(a),str(b),key=Decimal))+inflate)*GRID) for a,b in zip(u,v)]
        for a,b in self.fences:
            assert any(a[i]*GRID>H[i] or b[i]*GRID<L[i] for i in range(3))
        # Disjoint coordinate intervals are exact integer separators too.
        # Independently check all triangles, not the discovery index.
        T=self.T
        a=T.min(axis=1);b=T.max(axis=1)
        gap=np.maximum(a-H,np.asarray(L)-b).max(axis=1)
        rest=T[gap<=0]
        sure=float(gap[gap>0].min())/GRID if (gap>0).any() else float('inf')
        return min(sure,exact_separators(rest,L,H)) if len(rest) else sure
def section2(u,v,r):
    return [(min(u[i],v[i])-r,max(u[i],v[i])+r) for i in range(2)]
def search(m,start,goal,spine,positions,width=7):
    import heapq
    # Search within an authored band about the nominal route.
    allowed=set()
    slit=[section2(positions[a],positions[b],width) for a,b in zip(spine,spine[1:])]
    for (xmin,xmax),(ymin,ymax) in slit:
        for x in range(xmin,xmax+1):
            for y in range(ymin,ymax+1):allowed.add((x,y))
    def permitted(q):
        return tuple(q[:2]) in allowed and 2<=q[2]<=12
    def heur(q):
        return sum(abs(a-b) for a,b in zip(q,goal))
    assert permitted(start) and permitted(goal)
    q=[(heur(start),0,start)]
    dist={start:0};parent={start:None}
    while q:
      _,k,p=heapq.heappop(q)
      if k!=dist[p]:continue
      if p==goal:
        out=[]
        while p is not None:
            out.append(p);p=parent[p]
        return out[::-1],len(dist)
      for ax in range(3):
        for inc in (-1,1):
            j=list(p);j[ax]+=inc;j=tuple(j)
            if not permitted(j) or k+1>=dist.get(j,10**9):continue
            if not m.clear(*sorted([p,j])):continue
            parent[j]=p;dist[j]=k+1
            heapq.heappush(q,(k+1+heur(j),k+1,j))
    return None,len(dist)
def compress(path):
    if not path:return path
    def direction(p,q):return tuple(b-a for a,b in zip(p,q))
    return [path[0]]+[path[i] for i in range(1,len(path)-1)
                      if direction(path[i-1],path[i])!=direction(path[i],path[i+1])]+[path[-1]]
INPUTS={
 'far_short':((100,75,8),(0,0,6),[42,13,1,43,39,9,4,0]),
 'far_detour':((100,75,8),(0,0,6),[42,16,6,8,3,2,39,9,4,0]),
 'near':((75,100,6),(0,0,6),[6,8,3,2,39,9,4,0]),
 'installer':((100,50,8),(0,0,6),[13,1,43,39,9,4,0]),
}

def distance(a,b):return sum(abs(x-y) for x,y in zip(a,b))
def duration(p):
    def time(a,b):
        L=Decimal(distance(a,b))
        return 2*L.sqrt() if L<=9 else L/3+3
    return sum(time(a,b) for a,b in zip(p,p[1:]))
def clipped(p,box):
    a,b=box
    for q,r in zip(p,p[1:]):
        L=[min(x,y)*GRID-3005*GRID//10000 for x,y in zip(q,r)]
        H=[max(x,y)*GRID+3005*GRID//10000 for x,y in zip(q,r)]
        if all(a[i]*GRID<=H[i] and b[i]*GRID>=L[i] for i in range(3)):
            return True
    return False
GATE_A=(tuple(map(Decimal,('87.5','62.45','0'))),tuple(map(Decimal,('112.5','62.55','15'))))
GATE_B=(tuple(map(Decimal,('62.45','37.5','0'))),tuple(map(Decimal,('62.55','62.5','15'))))
PARK_B=((Decimal('-.3'),Decimal('-.3'),Decimal('5.7')),(Decimal('.3'),Decimal('.3'),Decimal('6.3')))
PARK_I=((Decimal('-.3'),Decimal('2.7'),Decimal('5.7')),(Decimal('.3'),Decimal('3.3'),Decimal('6.3')))
def run():
    import json
    verify()
    T,F,pos=load_scene()
    m=Map(T,F)
    print(len(T),'triangles across selected tiles;',len(F),'staging fences')
    read={}
    for label,(a,b,s) in INPUTS.items():
        p=list(map(tuple,json.loads((P/(label+'.json')).read_text())))
        assert p[0]==a and p[-1]==b
        if label=='installer':
            # Put the installer away from the courier's goal and egress.
            p=p[:-2]+[(0,3,p[-3][2]),(0,3,6)]
            assert p[-1]==(0,3,6)
        for h,k in zip(p,p[1:]):
            assert sum(x!=y for x,y in zip(h,k))==1,(label,h,k)
        bound=min(m.certificate(h,k) for h,k in zip(p,p[1:]))
        print(label, sum(distance(h,k) for h,k in zip(p,p[1:])),
              len(p)-1, f'{duration(p):.6f}', 'cap/stop seconds;', f'{bound:.8f}', 'mesh separation lower')
        read[label]=p
    assert clipped(read['far_short'],GATE_A)
    assert clipped(read['near'],GATE_B)
    assert not clipped(read['far_short'],GATE_B)
    assert not clipped(read['far_detour'],GATE_A)
    assert not clipped(read['near'],GATE_A)
    assert not clipped(read['installer'],GATE_A) and not clipped(read['installer'],GATE_B)
    assert all(not clipped(read[z],PARK_I) for z in ('far_short','far_detour','near'))
    # Parking during the other actor's movement is distinct from point
    # egress. Waiting at the two named starts does not obstruct the installer.
    for x,y,z in ((100,75,8),(75,100,6),(100,100,6)):
        cube=(tuple(Decimal(v)-Decimal('.3') for v in (x,y,z)),
              tuple(Decimal(v)+Decimal('.3') for v in (x,y,z)))
        assert not clipped(read['installer'],cube)
    from timeline import BRANCH
    extra=[]
    for label,p in BRANCH.items():
        bound=min(m.certificate(h,k) for h,k in zip(p,p[1:]))
        extra.append(bound)
    extra.append(m.certificate((100,50,8),(100,60,8)))
    # Pitched beam and elevated resident relay, independent of the two vehicles.
    extra.append(m.certificate(('99.94','57.95','8.18'),('100.06','64.05','8.40'),Decimal('.0005')))
    extra.append(m.certificate((100,50,9),(100,50,9),Decimal('.1505')))
    assert all(b>0 for b in extra)
    assert not clipped([(100,50,8),(100,60,8)],GATE_A)
    roof=(tuple(Decimal(k)-Decimal('.15') for k in (100,50,9)),
          tuple(Decimal(k)+Decimal('.15') for k in (100,50,9)))
    assert all(not clipped(p,roof) for p in (*read.values(),*BRANCH.values(),
                                             [(100,50,8),(100,60,8)]))
    print('authored gates/roof clearance and two-actor staging checks passed')
if __name__=='__main__':
    run()
