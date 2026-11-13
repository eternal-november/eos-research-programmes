import itertools,json
import numpy as np
from pathlib import Path
results=[]
for k in range(2,8):
    C=np.array(list(itertools.product([0,1],repeat=k)))
    r=np.array([.31+.05*i for i in range(k)])
    tau=np.array([.71-.03*i for i in range(k)])
    f=C.copy();f[:,1:]^=C[:,:-1]
    K=np.ones((len(C),len(C)))
    for i in range(k): K*=(1+tau[i]*(-1.)**(C[:,i,None]+f[None,:,i]))/2
    def obs_moment(ids):
        return np.prod(r[list(ids)])*(-1.)**C[:,list(ids)].sum(axis=1)
    def triple(ids0,ids1,ids2):
        return obs_moment(ids2)@K@(obs_moment(ids1)*(K@obs_moment(ids0)))/len(C)
    avec=[];cvec=[]
    for i in range(k):
        p=[] if i==0 else [i-1]
        a=triple([i]+p,[i],[])
        c=triple([i]+p,p,[i])
        rp=1 if i==0 else r[i-1]
        assert abs(a-tau[i]*r[i]**2*rp)<1e-12
        assert abs(c-tau[i]**2*r[i]**2*rp**2)<1e-12
        avec.append(a);cvec.append(c)
    rhat=np.array(avec)/np.sqrt(cvec)
    tauhat=np.array(cvec)/(np.array(avec)*np.r_[1,rhat[:-1]])
    assert max(abs(rhat-r))<1e-12
    assert max(abs(tauhat-tau))<1e-12
    results.append(dict(k=k,max_r_error=float(max(abs(rhat-r))),max_tau_error=float(max(abs(tauhat-tau))),passed=True))
Path(__file__).with_name('Heterogeneous_Pair_Path_QA.json').write_text(json.dumps(results,indent=2)+'\n')
print(json.dumps(results,indent=2))
