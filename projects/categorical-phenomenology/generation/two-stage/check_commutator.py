import itertools, json
import numpy as np


def orth(rng,r):
    return np.linalg.qr(rng.normal(size=(r,r)))[0]


def run(r):
    rng=np.random.default_rng(3701+r)
    q=r+1
    # Fixed simplex contrast basis, followed by arbitrary patch-specific rotations.
    H=np.eye(q)-np.ones((q,q))/q
    ev,U=np.linalg.eigh(H)
    U=U[:,np.argsort(ev)[-r:]]
    lam=1/(2*q*np.sqrt(r))
    A=[lam*U@orth(rng,r) for _ in range(4)]
    u=np.ones(q)/q
    cube=np.array(list(itertools.product([-1.,1.],repeat=r)))
    axes=np.concatenate([np.sqrt(r)*np.eye(r),-np.sqrt(r)*np.eye(r)])
    sources=[cube,np.concatenate([cube,axes])]
    weights=[np.ones(len(cube))/len(cube),np.r_[np.full(len(cube),r/(r+2)/len(cube)),np.full(2*r,2/(r+2)/(2*r))]]
    laws=[]
    for S,w in zip(sources,weights):
        P=[u[None,:]+S@Aj.T for Aj in A]
        assert min(p.min() for p in P)>=1/(2*q)-1e-12
        pairs={(i,j):np.einsum('s,sa,sb->ab',w,P[i],P[j]) for i in range(4) for j in range(4) if i!=j}
        triple=np.einsum('s,sa,sb,sc->abc',w,*P[:3],optimize=True)
        quartet=np.einsum('s,sa,sb,sc,sd->abcd',w,*P,optimize=True)
        laws.append((pairs,triple,quartet))
    pairgap=max(np.max(abs(laws[0][0][key]-laws[1][0][key])) for key in laws[0][0])
    triplegap=np.max(abs(laws[0][1]-laws[1][1]))
    D={key:val-np.outer(u,u) for key,val in laws[0][0].items()}
    G=D[0,1]@np.linalg.pinv(D[2,1],rcond=1e-10)@D[2,0]
    e,V=np.linalg.eigh((G+G.T)/2)
    idx=np.argsort(e)[-r:]
    B0=V[:,idx]*np.sqrt(e[idx])
    B=[B0]+[D[j,0]@np.linalg.pinv(B0).T for j in range(1,4)]
    maps=[np.linalg.pinv(Bj)@(np.eye(q)-u[:,None]*np.ones((1,q))) for Bj in B]
    g=np.eye(r)[0]
    h=(np.eye(r)[0]+np.eye(r)[1])/np.sqrt(2)
    norms=[]
    for _,_,J in laws:
        matrices=[]
        for v in (g,h):
            raw=np.einsum('abcd,ia,jb,c,d->ij',J,maps[0],maps[1],v@maps[2],v@maps[3],optimize=True)
            M=(raw+raw.T)/2-np.eye(r)-2*np.outer(v,v)
            matrices.append(M)
        M,N=matrices
        norms.append(float(np.linalg.norm(M@N-N@M,2)))
    expected=8/(r+2)**2
    assert pairgap<1e-12 and triplegap<1e-12
    assert norms[0]<1e-7
    assert abs(norms[1]-expected)<1e-7
    return dict(r=r,output_categories=q,source_support=len(sources[1]),pair_gap=float(pairgap),triple_gap=float(triplegap),independent_commutator_norm=norms[0],coupled_commutator_norm=norms[1],theoretical_norm=expected)

if __name__=='__main__':
    print(json.dumps([run(r) for r in [2,3,4,6,8]],indent=2))
