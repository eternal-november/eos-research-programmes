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
    assert len(out)==len(g)==3
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

def build():
    fields={v.findtext('name'):v.findtext('pose') for v in parse(P/'world.sdf').findall('.//include')}
    poses={6:(75,100,0),16:(100,100,0),42:(100,75,0)}
    meshes={}
    for idx,k in ((6,'corner'),(16,'tee'),(42,'straight')):
        vi=fields[f'tile_{idx}'].split()
        assert tuple(map(int,vi[:3]))==poses[idx] and abs(float(vi[-1]))==3.14159
        b=parse(P/(k+'.sdf'))
        unit=tuple(map(Decimal,b.findtext('.//collision/geometry/mesh/scale').split()))
        assert unit==((Decimal('1.005'),Decimal('1.005'),1) if idx!=42 else (1,1,1))
        assert b.findtext('.//collision/pose')=='0 0 0 0 0 0'
        L=parse(P/(k+'_lights.sdf')) if idx!=42 else None
        if L:
            assert L.findtext('.//include/pose') in (None,'0 0 0 0 0 0')
            assert L.findtext('.//include/uri').endswith(
                'Cave Corner 01 Type B' if idx==6 else 'Cave 3 Way 01 Type B')
        M=collada(P/(k+'.dae'),unit)
        assert float(np.abs(M[:,:,:2]).sum(axis=2).max())<31*GRID
        meshes[idx]=M*[-1,-1,1]+[int(t)*GRID for t in poses[idx]]
    return poses,meshes

def section(pts,z,a=.30):
    heads=np.min(pts,axis=0)
    tail=np.max(pts,axis=0)
    lo=(heads[0]-a,heads[1]-a,z-a)
    hi=(tail[0]+a,tail[1]+a,z+a)
    return lo,hi


def find_route(M,start,goal):
    # Restrict the development search to this lattice window. We do not
    # interpret failure in it as a physical impossibility.
    from collections import deque
    lo=M.min(axis=1);hi=M.max(axis=1)
    def margin(p,q):
        L,U=map(np.asarray,section((p,q),0.))
        # For a three-dimensional rectilinear step use the full z range.
        L[2]=min(p[2],q[2])-.3002
        U[2]=max(p[2],q[2])+.3002
        L[:2]-=.0002;U[:2]+=.0002
        mask=np.logical_and(hi>=L,lo<=U).all(axis=1)
        N=M[mask]
        return len(N)==0 or visual_margin(N,L,U)>1e-6
    parent={start:None};q=deque([start])
    while q:
        p=q.popleft()
        if p==goal:
            out=[]
            while p is not None:out.append(p);p=parent[p]
            return out[::-1]
        for axis,step in ((1,-1),(0,1),(0,-1),(2,1),(2,-1),(1,1)):
            r=list(p);r[axis]+=step;r=tuple(r)
            if r in parent:continue
            if 93<=r[0]<=107 and 75<=r[1]<=101 and 2<=r[2]<=11 and margin(p,r):
                parent[r]=p;q.append(r)
    return None


def audit():
    verify()
    poses,M=build()
    t=np.concatenate(tuple(M.values()))
    paths={
       6:[(100,100,6),(75,100,6)],
       42:[(100,100,6),(100,83,6),(101,83,6),(101,82,6),
           (102,82,6),(102,82,7),(102,75,7),(102,75,8),(100,75,8)]
    }
    # A valid route is not a claim about a faster, curved trajectory.
    # Selected exact certificates include a 0.2 mm rotation/input buffer.
    for u,l in paths.items():
        worst=100.
        count=0
        lengths=[]
        for a,b in zip(l,l[1:]):
            dx=[abs(x-y) for x,y in zip(a,b)]
            assert sum(x!=0 for x in dx)==1
            lengths.append(sum(dx))
            L=[min(x,y)*GRID-3002*GRID//10000 for x,y in zip(a,b)]
            H=[max(x,y)*GRID+3002*GRID//10000 for x,y in zip(a,b)]
            worst=min(worst,exact_separators(t,L,H))
            count+=len(t)
        assert worst>0.001
        assert tuple(poses[u][:2])==l[-1][:2]
        time=sum(2*(Decimal(z).sqrt()) if z<=9 else Decimal(z)/3+3 for z in lengths)
        assert (u==6 and 11<time<12) or (u==42 and 26<time<27)
        print('rest at each turn:',f'{time:.5f}','seconds in the declared model')
        print(u,sum(lengths),'meters',len(lengths),'segments',count,
              'triangle-box certificates',f'{worst:.5f}','lower bound')
    # For comparison, a native geometry vertex intrudes on the direct
    # altitude-8 straight surrogate; only a source-specific obstruction.
    # Use the tee vertex in nominal yaw and leave >0.2 mm in every
    # coordinate, which transports the strict witness through yaw.
    g=np.asarray(M[16]).reshape(-1,3)
    a=np.array([997002*GRID//10000, 747002*GRID//10000, 77002*GRID//10000], dtype=np.int64)
    b=np.array([1002998*GRID//10000,1002998*GRID//10000,82998*GRID//10000], dtype=np.int64)
    candidates=np.flatnonzero(np.logical_and(g>a,g<b).all(axis=1))
    w=None
    for idx in candidates:
        q=g[(idx//3)*3:(idx//3)*3+3].tolist()
        v=[k-j for k,j in zip(q[1],q[0])];z=[k-j for k,j in zip(q[2],q[0])]
        if any(v[j]*z[(j+1)%3]!=v[(j+1)%3]*z[j] for j in range(3)):
            w=g[idx]
            break
    assert w is not None
    print('direct 16-to-42 at z=8 contains a tee vertex:',tuple(round(float(x/GRID),7) for x in w))
if __name__=='__main__':
    import sys
    if '--search' in sys.argv:
        _,T=build()
        print(find_route(np.asarray(np.concatenate(tuple(T.values())),dtype=float)/GRID,(100,100,6),(100,75,8)))
    else:
        audit()
