"""Numerical sanity check of deterministic local inverse/table-error bounds.
This checks the stated inequalities on random finite fixtures. It is not a proof,
not a calibration-learning implementation, and not a finite-sample coverage study.
"""
import numpy as np
import json
from pathlib import Path
rng=np.random.default_rng(281022)
def norm1(a): return np.linalg.norm(a,1) if a.ndim==2 else abs(a).sum()
def kron_all(xs):
    z=np.array([1.])
    for x in xs: z=np.kron(z,x)
    return z
max_ratio=0.; max_inverse_ratio=0.; max_conditional_ratio=0.
for trial in range(50):
    r=3; s=5; k=3
    Es=[]; Ehs=[]
    for j in range(k):
        E=rng.random((s,r)); E/=E.sum(axis=0)
        # Reject ill-conditioned fixtures; no claim this lower bound is learned.
        while np.linalg.svd(E,compute_uv=False)[-1]<.08:
            E=rng.random((s,r)); E/=E.sum(axis=0)
        G=rng.random((s,r)); G/=G.sum(axis=0)
        Eh=.998*E+.002*G
        Es.append(E); Ehs.append(Eh)
    Ls=[np.linalg.pinv(E) for E in Es]; Lhs=[np.linalg.pinv(E) for E in Ehs]
    B=max([1.]+[norm1(L) for L in Ls])
    eta=max(norm1(Lh-L) for Lh,L in zip(Lhs,Ls))
    for E,Eh,L,Lh in zip(Es,Ehs,Ls,Lhs):
        sig=min(np.linalg.svd(E,compute_uv=False)[-1],np.linalg.svd(Eh,compute_uv=False)[-1])
        inversebound=np.sqrt(r)*(sig**-2+2*r*sig**-4)*abs(Eh-E).sum()
        assert norm1(Lh-L)<=inversebound+1e-12
        max_inverse_ratio=max(max_inverse_ratio,norm1(Lh-L)/inversebound)
    p=rng.random(r**k); p/=p.sum()
    obs=kron_all(Es)@p
    noise=rng.random(s**k); noise/=noise.sum()
    oh=.999*obs+.001*noise
    delta=norm1(oh-obs)
    ph=kron_all(Lhs)@oh
    bound=(B+eta)**k*delta+k*eta*(B+eta)**(k-1)
    actual=norm1(ph-p)
    assert actual<=bound+1e-10
    max_ratio=max(max_ratio,actual/bound)
    pp=np.maximum(ph,0); pp/=pp.sum()
    zeta=norm1(pp-p)
    P=p.reshape(r,r*r); Ph=pp.reshape(r,r*r)
    for c in range(r*r):
        mass=P[:,c].sum()
        if zeta<mass/2:
            err=norm1(Ph[:,c]/Ph[:,c].sum()-P[:,c]/mass)
            cbound=4*zeta/mass
            assert err<=cbound+1e-10
            max_conditional_ratio=max(max_conditional_ratio,err/cbound if cbound else 0)
result={'status':'PASS','seed':281022,'fixtures':50,'latent_rank':3,'sensor_symbols':5,'joint_mask_size':3,
        'max_inverse_error_to_bound_ratio':max_inverse_ratio,'max_joint_error_to_bound_ratio':max_ratio,
        'max_conditional_error_to_bound_ratio':max_conditional_ratio,
        'scope':'Random finite inequality checks, not a proof or implemented learner.'}
Path(__file__).with_name('Local_Error_Transfer_QA.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
