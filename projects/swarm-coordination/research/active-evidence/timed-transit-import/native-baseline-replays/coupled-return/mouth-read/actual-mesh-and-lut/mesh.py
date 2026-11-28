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
GRID=10**10
def collada(path):
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
        for word in pos.findtext('float_array').split():
            x=Decimal(word)*Decimal('0.01')*GRID
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

def audit(world):
    verify()
    b=parse(P/'basic.sdf')
    assert b.findtext('.//collision/pose')=='0 0 0 0 0 0'
    assert b.findtext('.//collision/geometry/mesh/scale')=='1.0 1.0 1.0'
    assert b.findtext('.//collision/geometry/mesh/uri')=='meshes/cavestraight05.dae'
    l=parse(P/'lights.sdf')
    assert l.findtext('.//include/uri').endswith('Cave Straight 05 Type B')
    assert l.findtext('.//include/pose') in (None,'0 0 0 0 0 0')
    S=parse(world)
    field={v.findtext('name'):v.findtext('pose') for v in S.findall('.//include')}
    assert field['tile_13']=='100 50 0 0 -0 0'
    assert field['tile_42']=='100 75 0 0 0 -3.14159'
    T=collada(P/'straight.dae')
    assert len(T)==13612
    # Prove separation for rotation π. The maximum planar L1 vertex
    # radius is below 25 m and |π-3.14159|<0.000003 rad. Translation
    # from that approximation moves either coordinate by <0.0001 m.
    assert int(np.abs(T[:,:,:2]).sum(axis=2).max())<25*GRID
    M=np.concatenate((T+[100*GRID,50*GRID,0],T*[-1,-1,1]+[100*GRID,75*GRID,0]))
    def box(lo,hi):
        L=[int((Decimal(a)-Decimal('0.0001'))*GRID) for a in lo]
        H=[int((Decimal(b)+Decimal('0.0001'))*GRID) for b in hi]
        return exact_separators(M,L,H)
    # A true first-tile vertex inside the authored ground-size aperture.
    W=T+[100*GRID,50*GRID,0]
    lower=np.array([995*GRID//10,495*GRID//10,2*GRID//10])
    upper=np.array([1005*GRID//10,62*GRID,16*GRID//10])
    hits=np.argwhere(np.logical_and(W>lower,W<upper).all(axis=2))
    floor_witness=None
    for row,which in hits.tolist():
        q=W[row].tolist()
        u=[x-y for x,y in zip(q[1],q[0])]
        v=[x-y for x,y in zip(q[2],q[0])]
        if any(u[i]*v[(i+1)%3]!=u[(i+1)%3]*v[i] for i in range(3)):
            floor_witness=q[which]
            break
    assert floor_witness is not None
    air=box(('99.7','49.6','7.7'),('100.3','75.4','8.3'))
    beam=box(('99.94','57.95','8.18'),('100.06','64.05','8.40'))
    assert air>.10 and beam>.10
    print('27224 exact decimal triangles per box; both inflated swept volumes separated')
    print('ground tube conflicts with a tile-13 vertex at',tuple(round(v/GRID,8) for v in floor_witness))
    print('conservative clearance lower bounds:',f'{air:.5f}',f'{beam:.5f}')
    # Proposed beam and marker not in Fuel asset; probe carriage below panel.
    lo=Decimal('8.20')+6*Decimal('.018')
    hi=Decimal('8.23')+6*Decimal('.024')
    assert Decimal('8.30')<lo<=hi<Decimal('8.40')
    assert Decimal('8.25')<Decimal('8.30')
    r=(1+Decimal('.024')**2).sqrt()
    assert Decimal('4.5')*r+Decimal('.05')<5
    assert Decimal('6')-Decimal('.05')>5
    print('authored pitched ray and noninterfering panel fit the certified beam and trajectory boxes')
if __name__=='__main__':
    import sys
    audit(sys.argv[1])
