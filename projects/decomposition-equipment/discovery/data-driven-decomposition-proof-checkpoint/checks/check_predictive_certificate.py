import itertools, json
import numpy as np
rng=np.random.default_rng(27102026)

def make_model():
    p=rng.dirichlet([2,2])
    K={}
    for a in range(2):
        z=np.stack([rng.dirichlet([2]*4).reshape(2,2) for _ in range(2)])
        for o in range(2): K[a,o]=z[:,o,:]
    return p,K

def perturb(model):
    p,K=model
    p2=(1-1e-4)*p+1e-4*rng.dirichlet([2,2])
    _,J=make_model()
    return p2,{z:(1-1e-4)*K[z]+1e-4*J[z] for z in K}

def prob(model,w):
    v=model[0].copy()
    for z in w: v=v@model[1][z]
    return float(v.sum())
P=[(),((0,0),)]
S=[(),((1,0),)]

def table(model):
    B=np.array([[prob(model,p+s) for s in S] for p in P])
    E={z:np.array([[prob(model,p+(z,)+s) for s in S] for p in P]) for z in model[1]}
    u=np.array([prob(model,s) for s in S]); v=np.array([prob(model,p) for p in P])
    return B,E,u,v

cases=0; identities=0; bounds=0
for _ in range(150):
    f=make_model(); g=perturb(f)
    F=table(f); G=table(g)
    sig=min(np.linalg.svd(F[0],compute_uv=False)[-1],np.linalg.svd(G[0],compute_uv=False)[-1])
    if sig<1e-5: continue
    eps=max(np.max(abs(F[0]-G[0])),np.max(abs(F[2]-G[2])),np.max(abs(F[3]-G[3])),*(np.max(abs(F[1][z]-G[1][z])) for z in F[1]))
    for model,T in [(f,F),(g,G)]:
        inv=np.linalg.inv(T[0]); alpha=T[2]@inv; M={z:E@inv for z,E in T[1].items()}; beta=T[3]
        for length in range(4):
            for w in itertools.product(list(M),repeat=length):
                row=alpha.copy()
                for z in w: row=row@M[z]
                assert abs(row@beta-prob(model,w))<1e-8
                identities+=1
    for H in range(1,7):
        # Deterministic adaptive controller: action parity of preceding outputs.
        laws=[]
        for model in [f,g]:
            out=[]
            for oo in itertools.product(range(2),repeat=H):
                w=[]; state=0
                for o in oo:
                    w.append((state,o)); state ^= o
                out.append(prob(model,tuple(w)))
            assert abs(sum(out)-1)<1e-10
            laws.append(np.array(out))
        tv=.5*np.abs(laws[0]-laws[1]).sum()
        r=2; k=1/sig; m=2
        bound=min(1,(2*r*k+r*r*k*k+H*m*(r*r*k*k+r**3*k**3))*eps)
        assert tv<=bound+1e-10,(tv,bound)
        bounds+=1
    cases+=1
print(json.dumps({'status':'PASS','model_pairs':cases,'finite_basis_word_identity_checks':identities,'adaptive_controller_TV_bounds':bounds,'note':'Finite numerical regression only; not proof or data-inference validation.'},indent=2))
