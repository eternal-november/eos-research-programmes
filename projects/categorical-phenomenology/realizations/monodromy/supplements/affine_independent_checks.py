from pathlib import Path
import numpy as np, json
rng=np.random.default_rng(20261103)
m,n,s=4,3,3
eps=1/24; beta=(s*eps+1/m)/2
Q=np.array([[1/np.sqrt(2),1/np.sqrt(6),1/np.sqrt(12)],[-1/np.sqrt(2),1/np.sqrt(6),1/np.sqrt(12)],[0,-2/np.sqrt(6),1/np.sqrt(12)],[0,0,-3/np.sqrt(12)]])
q=np.array([[1,1,1],[1,-1,-1],[-1,1,-1],[-1,-1,1]])/np.sqrt(3)
c=np.ones(m)/m; e0=np.ones(m)/np.sqrt(m)
out=dict(samples=10000,epsilon=eps,beta=beta,max_stochastic_product_error=0.,max_real_product_error=0.,max_row_sum_error=0.,min_stochastic_factor_entry=1.,min_H_entry=1.,min_third_singular_value=1.,max_fourth_singular_value=0.,min_orthant_distance_ratio=1.)
for j in range(out['samples']):
 x=rng.normal(size=n); x/=np.linalg.norm(x); P=np.eye(n)-np.outer(x,x)
 H=np.vstack([c,c+eps*P@Q.T])
 A=np.vstack([np.ones(s+1)/(s+1),(1+(s*eps/beta)*(P@q.T))/(s+1)])
 B=c+beta*(q@P@Q.T)
 Ar=np.vstack([x/2,x/2+eps*P]); Br=np.outer(x,e0)+P@Q.T
 out['max_stochastic_product_error']=max(out['max_stochastic_product_error'],float(np.max(np.abs(H-A@B))))
 out['max_real_product_error']=max(out['max_real_product_error'],float(np.max(np.abs(H-Ar@Br))))
 out['max_row_sum_error']=max(out['max_row_sum_error'],float(np.max(np.abs(A.sum(1)-1))),float(np.max(np.abs(B.sum(1)-1))))
 out['min_stochastic_factor_entry']=min(out['min_stochastic_factor_entry'],float(A.min()),float(B.min()))
 out['min_H_entry']=min(out['min_H_entry'],float(H.min()))
 sv=np.linalg.svd(H,compute_uv=False)
 out['min_third_singular_value']=min(out['min_third_singular_value'],float(sv[2])); out['max_fourth_singular_value']=max(out['max_fourth_singular_value'],float(sv[3]))
 z=Q@rng.normal(size=n); z/=np.linalg.norm(z)
 out['min_orthant_distance_ratio']=min(out['min_orthant_distance_ratio'],float(np.linalg.norm(np.minimum(z,0))),float(np.linalg.norm(np.maximum(z,0))))
out['proved_nonnegative_one_factor_gap']=eps/(2*m*np.sqrt(n))
out['proved_stochastic_one_factor_gap']=eps/(2*np.sqrt(n*m))
assert out['max_stochastic_product_error']<1e-12
assert out['max_real_product_error']<1e-12
assert out['min_stochastic_factor_entry']>0
assert out['max_row_sum_error']<1e-12
assert out['max_fourth_singular_value']<1e-12
assert out['min_third_singular_value']>0
assert out['min_orthant_distance_ratio']>=1/np.sqrt(m)-1e-12
with open(str(Path(__file__).resolve().with_name('affine_independent_checks.json')),'w') as f: json.dump(out,f,indent=2)
print(json.dumps(out,indent=2))
