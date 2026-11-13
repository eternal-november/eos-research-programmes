#!/usr/bin/env python3
"""Independent regression checks. Numerical tests supplement, not replace, proofs.
Run: python topology_finite_review_checks.py
Requires NumPy and SciPy; fixed seed makes every test reproducible.
"""
import itertools, json, math
from pathlib import Path
import numpy as np
from scipy.linalg import null_space

rng = np.random.default_rng(2026110320)
OUT = {}

def op(a):
    return float(np.linalg.norm(a, 2))

def frame(a, r):
    val, vec = np.linalg.eigh(a)
    return val[::-1], vec[:, -r:]

def random_orth(n):
    q, rr = np.linalg.qr(rng.normal(size=(n,n)))
    return q @ np.diag(np.where(np.diag(rr)<0,-1.,1.))

# A3, including repeated eigenvalues inside each spectral group.
max_ratio = 0.
for z in range(5000):
    m = int(rng.integers(2,11)); r = int(rng.integers(1,m))
    vals = np.sort(rng.uniform(-2,2,m))[::-1]
    if z % 3 == 0:
        vals[:r] = 1.; vals[r:] = -1.
    gap = vals[r-1]-vals[r]
    q = random_orth(m); A = (q*vals) @ q.T
    R = rng.normal(size=(m,m)); R = (R+R.T)/2
    e = gap * rng.uniform(.001,.499)
    R *= e/op(R)
    _, U = frame(A,r); _, V = frame(A+R,r)
    dist = op(U@U.T - V@V.T)
    bound = e/(gap-e)
    assert dist <= bound + 1e-10
    max_ratio = max(max_ratio, dist/bound)
OUT['ordered_gap_projector_trials'] = 5000
OUT['max_observed_distance_to_bound_ratio'] = max_ratio

# Arbitrary frame gauges near one actual space: determinant comparison and triangles.
min_cos = 1.; max_dist = 0.
for _ in range(2500):
    m = int(rng.integers(2,11)); r = int(rng.integers(1,m))
    P = np.diag([1.]*r+[0.]*(m-r))
    frames=[]; lifted=[]
    for j in range(3):
        Z = rng.normal(size=(m-r,r)); Z *= rng.uniform(.001,.352)/op(Z)
        raw = np.vstack([np.eye(r),Z]); Q,_=np.linalg.qr(raw)
        Q = Q @ random_orth(r)
        assert op(Q@Q.T-P) < 1/3
        D,W = np.linalg.eigh(Q.T@P@Q)
        F = P@Q@(W*(D**-.5))@W.T
        assert op(F.T@F-np.eye(r)) < 1e-10
        frames.append(Q); lifted.append(F)
    signs=[]
    for i,j in [(0,1),(1,2),(2,0)]:
        G=frames[i].T@frames[j]
        cos=float(np.linalg.svd(G,compute_uv=False)[-1]); min_cos=min(min_cos,cos)
        assert cos > math.sqrt(5)/3
        pert=op(frames[i].T@P@frames[j]-G); max_dist=max(max_dist,pert)
        assert pert < 1/3
        sign=int(np.sign(np.linalg.det(G)))
        assert sign == int(np.sign(np.linalg.det(lifted[i].T@lifted[j])))
        signs.append(sign)
    assert math.prod(signs)==1
OUT['overlap_triangle_trials']=2500
OUT['minimum_observed_overlap_singular_value']=min_cos
OUT['maximum_observed_transition_perturbation']=max_dist

# Minimal six-vertex triangulated RP2: exact mod-2 topology and AW cup squares.
facets=[(1,2,3),(1,2,4),(1,3,5),(1,4,6),(1,5,6),
        (2,3,6),(2,4,5),(2,5,6),(3,4,5),(3,4,6)]
edges=sorted({e for f in facets for e in itertools.combinations(f,2)})
assert len(edges)==15
assert all(sum(set(e)<=set(f) for f in facets)==2 for e in edges)
# Each vertex link is a connected cycle; Euler characteristic is one.
for v in range(1,7):
    link=[tuple(x for x in f if x!=v) for f in facets if v in f]
    vertices=set(sum((list(e) for e in link),[]))
    assert all(sum(x in e for e in link)==2 for x in vertices)
    reached={next(iter(vertices))}
    for _ in vertices:
        reached |= {x for e in link if reached.intersection(e) for x in e}
    assert reached==vertices
assert 6-15+10==1
idx={e:i for i,e in enumerate(edges)}
def edge(a,u,v): return (a>>idx[tuple(sorted((u,v)))])&1
cobounds=set()
for mask in range(64):
    cobounds.add(sum((((mask>>(u-1))^(mask>>(v-1)))&1)<<i for i,(u,v) in enumerate(edges)))
cocycles=[]
for a in range(1<<15):
    if all(sum(edge(a,u,v) for u,v in itertools.combinations(f,2))%2==0 for f in facets):
        cocycles.append(a)
assert len(cocycles)==64 and len(cobounds)==32
cup_count=0
for perm in itertools.permutations(range(1,7)):
    order={v:i for i,v in enumerate(perm)}
    oriented=[sorted(f,key=order.get) for f in facets]
    for a in cocycles:
        cup=sum(edge(a,f[0],f[1])*edge(a,f[1],f[2]) for f in oriented)%2
        assert cup == (a not in cobounds)
        cup_count+=1
OUT['rp2_exact_cocycle_count']=len(cocycles)
OUT['rp2_exact_coboundary_count']=len(cobounds)
OUT['rp2_cup_evaluations_all_vertex_orders']=cup_count

# Exact-node analytic partition interpolation, random stochastic factors.
interp_count=0
for _ in range(300):
    N=int(rng.integers(2,9)); d=int(rng.integers(2,6))
    U=rng.dirichlet(np.ones(2),size=(N,d+1))
    V=rng.dirichlet(np.ones(d+1),size=(N,2))
    points=rng.normal(size=(N,d)); points/=np.linalg.norm(points,axis=1)[:,None]
    embedded=np.array([np.outer(u,u).ravel() for u in points])
    queries=list(embedded)
    for j in range(10):
        u=rng.normal(size=d);u/=np.linalg.norm(u); queries.append(np.outer(u,u).ravel())
    for j,x in enumerate(queries):
        dist=((embedded-x)**2).sum(axis=1)
        weights=np.array([np.prod(np.delete(dist,i)) for i in range(N)])
        assert weights.sum()>0
        weights/=weights.sum()
        Ui=np.einsum('n,npk->pk',weights,U);Vi=np.einsum('n,nkm->km',weights,V)
        assert np.min(Ui)>0 and np.min(Vi)>0
        assert np.max(abs(Ui.sum(axis=1)-1))<1e-12
        assert np.max(abs(Vi.sum(axis=1)-1))<1e-12
        if j<N:
            assert np.max(abs(Ui@Vi-U[j]@V[j]))<1e-12
        interp_count+=1
OUT['analytic_interpolation_point_checks']=interp_count

# Smooth seam alternatives: algebra, rank, sign descent, all-action kernels.
def cutoff(x,eta):
    lo=eta/3
    if x<=lo:return 0.
    if x>=eta:return 1.
    t=(x-lo)/(eta-lo)
    a=math.exp(-1/t);b=math.exp(-1/(1-t))
    return a/(a+b)
def seam(u,v,eta):
    t=float(u@v);f=cutoff(abs(t),eta)
    return f*np.sign(t)*u+(1-f)*v

def factors(z,A,alpha,delta):
    m=len(z);c=np.ones(m)/m
    co=A.T@z
    U=np.column_stack([(1+alpha*co)/2,(1-alpha*co)/2])
    U=np.vstack([[.5,.5],U])
    V=np.vstack([c+delta*z,c-delta*z])
    return U,V

outside_count=0;word_count=0;min_norm=1.;max_rank_tail=0.
S=np.array([[0.,1.],[1.,0.]])
J=np.ones((2,2))/2
for _ in range(2500):
    d=int(rng.integers(1,7));m=d+2
    A=null_space(np.ones((1,m)))
    uv=rng.normal(size=(2,d+1));uv/=np.linalg.norm(uv,axis=1)[:,None]
    u,v=uv
    eta=float(rng.uniform(.02,.8));z=seam(u,v,eta)
    assert np.max(abs(z-seam(-u,v,eta)))<1e-12
    assert op(z[:,None])<=1+1e-12 and z@v>0
    assert float(z@z)>=.5-1e-12
    min_norm=min(min_norm,float(np.linalg.norm(z)))
    alpha=.4;delta=1/(2*m)
    prep,em=factors(A@z,A,alpha,delta)
    H=prep@em
    centered=H[1:]-H[0]
    sv=np.linalg.svd(centered,compute_uv=False)
    assert sv[0]>=alpha*delta/2-1e-12
    assert sv[1]<1e-12
    max_rank_tail=max(max_rank_tail,float(sv[1]))
    assert np.min(prep)>0 and np.min(em)>0
    assert np.max(abs(prep.sum(1)-1))<1e-12
    assert np.max(abs(em.sum(1)-1))<1e-12
    if abs(u@v)>=eta:
        outside_count+=1
        tp,te=factors(A@u,A,alpha,delta)
        assert np.max(abs(H-tp@te))<1e-12
        R=np.eye(2) if u@v>0 else S
        assert np.max(abs(prep-tp@R))<1e-12
        for action in [np.eye(2),S,J]:
            for y in range(m):
                M=action@np.diag(em[:,y]); Mt=action@np.diag(te[:,y])
                assert np.max(abs(M-R@Mt@R))<1e-12
        for _ in range(5):
            i=int(rng.integers(0,m));left=prep[i].copy();right=tp[i].copy()
            for t in range(int(rng.integers(1,13))):
                action=[np.eye(2),S,J][int(rng.integers(0,3))]
                y=int(rng.integers(0,m))
                left=left@action@np.diag(em[:,y]);right=right@action@np.diag(te[:,y])
            assert abs(left.sum()-right.sum())<1e-12
            word_count+=1
OUT['smooth_seam_trials']=2500
OUT['outside_band_all_instrument_conjugacy_trials']=outside_count
OUT['controlled_word_checks']=word_count
OUT['minimum_observed_seam_norm']=min_norm
OUT['maximum_observed_centered_second_singular_value']=max_rank_tail

# Exact interval-union band probability on RP1; union bound in coupling proof.
for _ in range(2500):
    N=int(rng.integers(1,51));eta=float(rng.uniform(.0001,.5));radius=math.asin(eta)
    angles=rng.uniform(0,math.pi,N); intervals=[]
    for angle in angles:
        center=(angle+math.pi/2)%math.pi
        for shift in [-math.pi,0.,math.pi]:
            a=max(0.,center+shift-radius);b=min(math.pi,center+shift+radius)
            if a<b:intervals.append((a,b))
    intervals.sort();end=0.;length=0.
    for a,b in intervals:
        if b>end:length+=b-max(a,end);end=b
    assert length/math.pi <= min(1.,N*2*radius/math.pi)+1e-12
OUT['circle_band_union_probability_checks']=2500
OUT['status']='all passed'
path=Path(__file__).with_name('topology_finite_review_checks_results.json')
path.write_text(json.dumps(OUT,indent=2)+'\n')
print(json.dumps(OUT,indent=2))
