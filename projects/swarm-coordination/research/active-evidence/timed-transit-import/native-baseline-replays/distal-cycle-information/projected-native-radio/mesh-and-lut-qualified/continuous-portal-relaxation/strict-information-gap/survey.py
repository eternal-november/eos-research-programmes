from pathlib import Path
from hashlib import sha256
from xml.etree.ElementTree import parse
import numpy as np
from decimal import Decimal
import sys
P=Path(sys.argv[1]).resolve()
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
        matrix=list(map(Decimal,node.findtext("matrix").split()))
        translation=[matrix[i] for i in (3,7,11)]
        for i in (3,7,11):matrix[i]=0
        assert list(matrix)==[int(i%5==0) for i in range(16)]
        m=g[node.find('instance_geometry').attrib['url'][1:]].find('mesh')
        sources={e.attrib['id']:e for e in m.findall('source')}
        vertices=m.find('vertices')
        assert sum(v.get('semantic')=='POSITION' for v in vertices)==1
        pos=sources[next(v for v in vertices if v.get('semantic')=='POSITION').get('source')[1:]]
        assert pos.find('technique_common/accessor').get('stride')=='3'
        points=[]
        for j,word in enumerate(pos.findtext('float_array').split()):
            x=(Decimal(word)+translation[j%3])*Decimal('0.01')*GRID*scale[j%3]
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
    assert out and len(out)==len(g)
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

from fractions import Fraction
import json
from itertools import pairwise

ids=(103,104,105,106,107,108,114,115,116,117,118,119,121,122,124,128,130,132,156,157)

def fields(root,name,kind='0 0 0 0 0 0'):
    return tuple(map(Decimal,root.findtext(name,kind).split()))

def source():
    d={e.findtext("name"):e for e in parse(P/"world.sdf").findall(".//include")}
    types={}; tri=[]; poses={}; by_tile={}
    for i in ids:
        e=d[f"tile_{i}"]
        name=e.findtext("uri").rsplit("/",1)[1].replace(" ","_")
        if name not in types:
            r=parse(P/(name+".sdf"))
            [(link,c)]=[(link,c) for link in r.findall(".//link") for c in link.findall("collision")]
            assert fields(link,"pose")==fields(c,"pose")==tuple([0]*6)
            sc=fields(c,"geometry/mesh/scale")
            assert c.findtext("geometry/mesh/uri").endswith(".dae")
            types[name]=collada(P/(name+".dae"),sc)
        x,y,z,a,b,yaw=fields(e,"pose")
        assert a==b==0
        q=round(float(yaw)/(np.pi/2))
        err=abs(float(yaw)-q*np.pi/2)
        assert err<.000004
        t=types[name]
        dx,dy,dz=t.transpose(2,0,1)
        rot=((dx,dy),(-dy,dx),(-dx,-dy),(dy,-dx))[q%4]
        assert int(np.max(abs(dx)+abs(dy)))<110*GRID
        by_tile[i]=np.stack((*rot,dz),axis=2)+np.array([int(v*GRID) for v in (x,y,z)])
        tri.append(by_tile[i])
        poses[i]=tuple(map(int,(x,y,z)))
    return np.concatenate(tri),poses,types,by_tile

def intersections(T,x,y):
    x*=GRID;y*=GRID
    lo=T.min(axis=1);hi=T.max(axis=1)
    out=set()
    mask=(lo[:,0]<=x)&(hi[:,0]>=x)&(lo[:,1]<=y)&(hi[:,1]>=y)
    for (ax,ay,az),(bx,by,bz),(cx,cy,cz) in T[mask].tolist():
        s=(by-cy)*(ax-cx)+(cx-bx)*(ay-cy)
        if not s:continue
        u=(by-cy)*(x-cx)+(cx-bx)*(y-cy)
        v=(cy-ay)*(x-cx)+(ax-cx)*(y-cy)
        if s<0:s,u,v=-s,-u,-v
        if u<0 or v<0 or u+v>s:continue
        out.add(Fraction(u*az+v*bz+(s-u-v)*cz,s*GRID))
    return sorted(out)

def run():
    verify()
    T,poses,types,by_tile=source()
    m=Map(T,[])
    out={}
    for i in (103,104,105,107,117,118,115,119,132):
        x,y,z=poses[i]
        hits=intersections(T,x,y)
        choices=[]
        for h in range(z,z+13):
            below=max((a for a in hits if a<h),default=None)
            above=min((a for a in hits if a>h),default=None)
            if below is None or above is None or min(h-below,above-h)<Fraction(3,4):continue
            p=(x,y,h)
            if not m.clear(p,p):continue
            low=m.certificate(p,p)
            assert low>0
            choices.append([h,round(float(below),6),round(float(above),6),round(low,9)])
        vv=[]
        if not choices:
            offsets=sorted((dx*dx+dy*dy,dx,dy)
              for dx in range(-12,13) for dy in range(-12,13))
            for _,dx,dy in offsets:
              local=intersections(by_tile[i],x+dx,y+dy)
              if len(local)<2:continue
              for h in range(z,z+13):
                below=max((k for k in local if k<h),default=None)
                above=min((k for k in local if k>h),default=None)
                if below is None or above is None or min(h-below,above-h)<Fraction(3,4):continue
                p=(x+dx,y+dy,h)
                if not m.clear(p,p):continue
                vv.append([list(p),round(float(below),6),round(float(above),6),round(m.certificate(p,p),9)])
                break
              if vv:break
        out[i]={"origin":poses[i],"hits_near":len([a for a in hits if z-6<=a<=z+14]),
            "bracketed_box": choices[:1],"shifted_box":vv}
    # An axis-aligned swept cube on the vertical chord between the
    # two individually clear stacked sites contains this actual mesh
    # vertex with > 0.5 mm horizontal room (the snap uncertainty).
    assert out[115]["bracketed_box"][0][0]==13 and out[119]["bracketed_box"][0][0]==34
    vertices=T.reshape(-1,3)
    ii=(np.abs(vertices[:,0]-325*GRID)<299*GRID//1000)&(np.abs(vertices[:,1]+250*GRID)<299*GRID//1000)&(vertices[:,2]>14*GRID)&(vertices[:,2]<33*GRID)
    hit=vertices[ii]
    assert len(hit)>0
    point=sorted(map(tuple,hit.tolist()))[0]
    print(json.dumps(dict(triangles=len(T),chord_collision_vertex=point,types={k:len(v) for k,v in sorted(types.items())},
                sites=out),sort_keys=True))
if __name__=="__main__":run()
