import json
import numpy as np
from pathlib import Path
rng=np.random.default_rng(20261103)
def basis(m):
    D=np.vstack([np.eye(m-1),-np.ones((1,m-1))])
    return np.linalg.qr(D)[0]
worst={k:0.0 for k in ['row_sum_error','rank2_residual','local_factor_error','retraction_error','descent_error','dynamic_sum_error','dynamic_word_error','native_read_error','strict_global_factor_error','tangent_factor_error','tangent_frame_error','tangent_real_factor_error']}
mins={'H':1.,'two_state_preparation':1.,'two_state_emission':1.,'strict_global_A':1.,'strict_global_B':1.,'tangent_U':1.,'tangent_V':1.}
for d in [0,1,2,3,5,9]:
    m=d+2; T=basis(m); c=np.ones(m)/m; alpha=.7; delta=1/(2*m); beta=alpha*delta; eta=.5/np.sqrt(m*(m-1)); S=np.array([[0,1],[1,0]]); J=np.ones((2,2))/2
    for sample in range(80):
        v=rng.normal(size=m-1); v/=np.linalg.norm(v); u=T@v
        H=np.vstack([c,c+beta*v[:,None]*u])
        Pprep=np.vstack([[.5,.5],np.column_stack([(1+alpha*v)/2,(1-alpha*v)/2])])
        E=np.vstack([c+delta*u,c-delta*u])
        def ql(u):
            q=np.vstack([np.maximum(u-eta,0),np.maximum(-u-eta,0)]); q/=q.sum(axis=1)[:,None]
            h=np.clip(u/eta,-1,1); L=np.column_stack([(1+h)/2,(1-h)/2]); return q,L
        Q,L=ql(u); Qm,Lm=ql(-u)
        MX=[[G@np.diag(E[:,y]) for y in range(m)] for G in [np.eye(2),S,J]]
        X=[[L@M@Q for M in mats] for mats in MX]
        Em=E[::-1]; MXm=[[G@np.diag(Em[:,y]) for y in range(m)] for G in [np.eye(2),S,J]]
        Xm=[[Lm@M@Qm for M in mats] for mats in MXm]
        worst['row_sum_error']=max(worst['row_sum_error'],float(abs(H.sum(1)-1).max()))
        sv=np.linalg.svd(H,compute_uv=False)
        if m>2: worst['rank2_residual']=max(worst['rank2_residual'],float(sv[2]))
        worst['local_factor_error']=max(worst['local_factor_error'],float(abs(Pprep@E-H).max()))
        worst['retraction_error']=max(worst['retraction_error'],float(abs(Q@L-np.eye(2)).max()))
        worst['descent_error']=max(worst['descent_error'],max(float(abs(X[a][y]-Xm[a][y]).max()) for a in range(3) for y in range(m)))
        worst['dynamic_sum_error']=max(worst['dynamic_sum_error'],max(float(abs(sum(X[a]).sum(1)-1).max()) for a in range(3)))
        native=np.column_stack([Pprep@Q@X[0][y]@np.ones(m) for y in range(m)])
        worst['native_read_error']=max(worst['native_read_error'],float(abs(native-H).max()))
        for trial in range(15):
            p=Pprep[rng.integers(m)]; pn=p@Q
            for step in range(rng.integers(1,9)):
                a=rng.integers(3); y=rng.integers(m); p=p@MX[a][y];pn=pn@X[a][y]
            worst['dynamic_word_error']=max(worst['dynamic_word_error'],float(abs(p.sum()-pn.sum())))
        lam=.5*m*H.min(); B=(1-lam)*np.eye(m)+lam*np.ones((m,m))/m; Af=(H-lam*np.ones((m,m))/m)/(1-lam)
        worst['strict_global_factor_error']=max(worst['strict_global_factor_error'],float(abs(Af@B-H).max()))
        for name,arr in [('H',H),('two_state_preparation',Pprep),('two_state_emission',E),('strict_global_A',Af),('strict_global_B',B)]:mins[name]=min(mins[name],float(arr.min()))
        # exact sharp singular-value lower bound, evaluated cancellation-free
        sigma2star=2*beta**2/m/(1+beta**2+np.sqrt((1+beta**2)**2-4*beta**2/m))
        assert sv[1]**2>=sigma2star-1e-12
# General-bundle upper construction and tangent-sphere real trivialization.
m=4; T=basis(m); c=np.ones(m)/m; e=np.ones(m)/np.sqrt(m); beta=.02;delta=.1
Z=np.sqrt(m/(m-1))*T
for sample in range(500):
    x=rng.normal(size=3);x/=np.linalg.norm(x);P=np.eye(3)-np.outer(x,x)
    H=np.vstack([c,c+beta*P@T.T])
    V=c+delta*Z@P@T.T
    U=np.vstack([np.ones(4)/4,(1+3*(beta/delta)*P@Z.T)/4])
    F=np.outer(e,x)+T@P
    worst['tangent_factor_error']=max(worst['tangent_factor_error'],float(abs(U@V-H).max()))
    worst['tangent_frame_error']=max(worst['tangent_frame_error'],float(abs(F.T@F-np.eye(3)).max()))
    worst['tangent_real_factor_error']=max(worst['tangent_real_factor_error'],float(abs((H@F)@F.T-H).max()))
    mins['tangent_U']=min(mins['tangent_U'],float(U.min()));mins['tangent_V']=min(mins['tangent_V'],float(V.min()))
assert max(worst.values())<1e-12
assert min(mins.values())>0
out={'status':'pass','proof_scope':'Numerical consistency checks only, not proof of topology or literature novelty.','dimensions_d':[0,1,2,3,5,9],'samples_per_d':80,'random_words_per_sample':15,'word_lengths':'1 to 8','tangent_sphere_samples':500,'max_errors':worst,'minimum_entries':mins}
Path(__file__).with_name('topology_audit_checks.json').write_text(json.dumps(out,indent=2))
print(json.dumps(out,indent=2))
