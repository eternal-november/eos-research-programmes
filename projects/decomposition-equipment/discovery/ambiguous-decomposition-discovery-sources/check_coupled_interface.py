"""Eight-state H-only QA fixture, not the discovery algorithm or full X/H test."""
import itertools,json
import numpy as np
states=np.array(list(itertools.product([-1.,1.],repeat=3)))
P=np.roll(np.eye(3),1,axis=1)
A=.3*P+.1*(P@P)
K=np.array([[np.prod((1+y*(A@x))/2) for y in states] for x in states])
Q=K.T-np.eye(8); Q[-1]=1; rhs=np.zeros(8);rhs[-1]=1
pi=np.linalg.solve(Q,rhs)
C=states.T@np.diag(pi)@states
G=np.diag([.001,.0015,.002])
# Compute H lag covariances directly from its finite transition matrix.
Gamma=[]
for lag in [1,2]:
    CH=states.T@np.linalg.matrix_power(K,lag).T@np.diag(pi)@states
    Gamma.append(G@CH@G)
B=Gamma[1]@np.linalg.inv(Gamma[0]);S=np.linalg.solve(B,Gamma[0])
g=np.sqrt(np.diag(S)); recovered=np.diag(1/g)@B@np.diag(g)
res={'scope':'isolated 3-spin H model, 8 states; positive gain observables supplied synthetically; not full residual-process simulation', 'mean_max_error':float(np.max(np.abs(pi@states))), 'stationarity_error':float(np.max(np.abs(pi@K-pi))), 'min_covariance_eigenvalue':float(np.linalg.eigvalsh(C).min()), 'A_max_recovery_error':float(np.max(np.abs(recovered-A))), 'gain_max_recovery_error':float(np.max(np.abs(g-np.diag(G))))}
assert res['A_max_recovery_error']<1e-12 and res['gain_max_recovery_error']<1e-12
print(json.dumps(res,indent=2))
