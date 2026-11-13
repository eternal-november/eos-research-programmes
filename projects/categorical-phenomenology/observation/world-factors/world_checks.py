#!/usr/bin/env python3
"""Finite checks for the world-domain branch. No simulations used for exact claims."""
import itertools, json, math
from pathlib import Path
import numpy as np
from scipy.optimize import linprog

HERE=Path(__file__).resolve().parent

def cube(m): return np.asarray(list(itertools.product((-1,1), repeat=m)),dtype=int)
def marginal_matrix(X, contexts):
    rows=[]
    for C in contexts:
        for a in itertools.product((-1,1),repeat=len(C)):
            rows.append(np.all(X[:,C]==np.array(a),axis=1).astype(float))
    return np.array(rows)
def bounds(A,b,f):
    lo=linprog(f,A_eq=A,b_eq=b,bounds=(0,None),method='highs')
    hi=linprog(-f,A_eq=A,b_eq=b,bounds=(0,None),method='highs')
    if not lo.success or not hi.success: return None
    return [float(lo.fun),float(-hi.fun)]
def feasible_support(A,b):
    out=[]
    for j in range(A.shape[1]):
        f=np.zeros(A.shape[1]); f[j]=-1
        sol=linprog(f,A_eq=A,b_eq=b,bounds=(0,None),method='highs')
        if sol.success and -sol.fun>1e-9:out.append(j)
    return out

results={}
# Full proper-subset marginals leave parity unconstrained.
parity=[]
for m in range(2,8):
    X=cube(m); contexts=[tuple(j for j in range(m) if j!=i) for i in range(m)]
    A=marginal_matrix(X,contexts)
    chi=np.prod(X,axis=1)
    plus=(chi==1)/2**(m-1); minus=(chi==-1)/2**(m-1)
    assert np.allclose(A@plus,A@minus)
    assert np.linalg.matrix_rank(A)==2**m-1
    bd=bounds(A,A@plus,chi)
    assert np.allclose(bd,[-1,1])
    parity.append({'m':m,'rank':int(np.linalg.matrix_rank(A)),'fiber_dimension':1,'parity_bounds':bd})
results['parity']=parity
# A generic chain panel has two missing interactions, but support collapse removes both.
X=cube(3); contexts=[(0,1),(1,2)]; A=marginal_matrix(X,contexts)
uniform=np.ones(8)/8
assert np.linalg.matrix_rank(A)==6
q=np.all(X==X[:,0,None],axis=1).astype(float)/2
S=feasible_support(A,A@q)
assert len(S)==2 and np.linalg.matrix_rank(A[:,S])==2
triple=np.prod(X,axis=1)
results['chain']={'generic_rank':6,'generic_fiber_dimension':2,'generic_triple_bounds':bounds(A,A@uniform,triple),'collapsed_support':[X[j].tolist() for j in S],'collapsed_triple_bounds':bounds(A,A@q,triple)}
# All three pair contexts can be locally consistent but globally impossible.
C=[(0,1),(1,2),(0,2)]; B=marginal_matrix(X,C)
b=np.tile([0,.5,.5,0],3)
sol=linprog(np.zeros(8),A_eq=B,b_eq=b,bounds=(0,None),method='highs')
assert not sol.success
results['negative_triangle']={'feasible':False,'solver_status':int(sol.status)}
# Exact sharp TV bounds under two symmetric pair error rates .02 and .03.
eps=[.02,.03]
pdis=np.zeros(8); pnest=np.zeros(8)
idx={tuple(x):i for i,x in enumerate(X)}
for root in (-1,1):
    for (e1,e2),p in { (0,0):.95,(1,0):.02,(0,1):.03}.items():
        vals=(root,root*(-1)**e1,root*(-1)**(e1+e2))
        pdis[idx[vals]]+=p/2
    for (e1,e2),p in {(0,0):.97,(1,1):.02,(0,1):.01}.items():
        vals=(root,root*(-1)**e1,root*(-1)**(e1+e2))
        pnest[idx[vals]]+=p/2
assert np.allclose(A@pdis,A@pnest)
bad=1-np.all(X==X[:,0,None],axis=1).astype(float)
TV=lambda p,r:float(.5*np.abs(p-r).sum())
bd=bounds(A,A@pdis,bad)
assert np.allclose(bd,[.03,.05])
assert np.isclose(TV(pdis,q),.05) and np.isclose(TV(pnest,q),.03)
results['sharp_tree_tv']={'pair_errors':eps,'compatible_global_tv_interval':bd,'disjoint_error_world_tv':TV(pdis,q),'nested_error_world_tv':TV(pnest,q)}
# Exhaustive small distributions verify retraction TV identity and union bound.
rng=np.random.default_rng(20261103)
max_error=0
for m in range(2,8):
    X=cube(m); n=2**m
    for _ in range(100):
        p=rng.dirichlet(np.ones(n)); signs=rng.choice((-1,1),size=m-1)
        maps=np.cumprod(np.r_[1,signs]); coherent=np.all(X==X[:,0,None]*maps,axis=1)
        q=np.zeros(n)
        for z in (-1,1):
            q[np.flatnonzero(np.all(X==z*maps,axis=1))[0]]=p[X[:,0]==z].sum()
        errors=[p[X[:,i+1]!=signs[i]*X[:,i]].sum() for i in range(m-1)]
        err=abs(TV(p,q)-p[~coherent].sum()); max_error=max(max_error,err)
        assert err<1e-12 and TV(p,q)<=sum(errors)+1e-12
results['retraction_checks']={'cases':600,'max_numerical_error':max_error}
# Exact coding-based observable coset count (6 bits, copy chains in two components).
m=6; X=cube(m)
# constraints x0=x1=x2, x3=x4=x5; only single-coordinate observations
support=np.all(X[:,:3]==X[:,0,None],axis=1)&np.all(X[:,3:]==X[:,3,None],axis=1)
A=marginal_matrix(X,[(i,) for i in range(m)])
assert support.sum()==4 and np.linalg.matrix_rank(A[:,support])==3
results['two_factors_unidentified_coupling']={'support_size':int(support.sum()),'observable_rank':int(np.linalg.matrix_rank(A[:,support])),'remaining_affine_dimension':1}
# Numerical costs for one-sided certificate and matching testing lower bound.
m=20; k=m-1; eps=.025; delta=.025; eta=.025
upper=math.ceil(k*math.log(1/delta)/eps)
root_samples=math.ceil(math.log(2/delta)/(2*eta**2))
kl=(1-delta)*math.log((1-delta)/delta)+delta*math.log(delta/(1-delta))
lower=k*kl/(-math.log(1-eps))
results['sample_cost']={'m':m,'joint_outcomes':2**m,'training_samples':k,'relation_tolerance':eps,'root_tolerance':eta,'relation_error_probability':delta,'root_error_probability':delta,'validation_samples':upper,'root_samples':root_samples,'total':k+upper+root_samples,'null_expected_lower_bound_for_fixed_tree_testing':lower}
(HERE/'world_checks_results.json').write_text(json.dumps(results,indent=2)+'\n')
print(json.dumps(results,indent=2))
# Fractional context cut-cover LP, including a dual certificate.
def cut_incidence(m, contexts):
    # Pin vertex 0 outside B to remove complementary duplicates.
    cuts=[frozenset(i+1 for i,b in enumerate(bits) if b) for bits in itertools.product((0,1),repeat=m-1) if any(bits)]
    M=np.array([[float(bool(set(C)&B) and bool(set(C)-B)) for C in contexts] for B in cuts])
    return cuts,M

def cut_lp(m,contexts):
    cuts,M=cut_incidence(m,contexts)
    p=linprog(np.ones(len(contexts)),A_ub=-M,b_ub=-np.ones(len(cuts)),bounds=(0,None),method='highs')
    if not p.success: return math.inf,None
    d=linprog(-np.ones(len(cuts)),A_ub=M.T,b_ub=np.ones(len(contexts)),bounds=(0,None),method='highs')
    assert d.success and abs(p.fun+d.fun)<1e-8
    tau=float(p.fun); w=p.x
    assert abs(np.min(M@(w/tau))-1/tau)<1e-8
    return tau,w

lp_checks=[]
for m in range(2,9):
    tree=[(i,i+1) for i in range(m-1)]
    tau,_=cut_lp(m,tree); assert abs(tau-(m-1))<1e-8
    for k in range(2,m+1):
        contexts=list(itertools.combinations(range(m),k)); tau,w=cut_lp(m,contexts)
        assert abs(tau-m/k)<1e-8
        lp_checks.append({'m':m,'k':k,'tau':tau})
    tau,_=cut_lp(m,[(i,) for i in range(m)]);assert math.isinf(tau)
results['cut_lp_complete_contexts']=lp_checks
# Direct checks of context KL for balanced cut-mixture alternatives.
kl_errors=[]
for m in range(2,7):
    X=cube(m); s=np.ones(m,dtype=int); null=np.all(X==X[:,0,None],axis=1).astype(float)/2
    cuts,_=cut_incidence(m,[(0,1)])
    for B in cuts:
        v=s.copy();v[list(B)]=-1
        qb=(np.all(X==v,axis=1)|np.all(X==-v,axis=1)).astype(float)/2
        alt=.9*null+.1*qb
        assert abs(TV(alt,null)-.1)<1e-12
        for k in range(1,m+1):
            for C in itertools.combinations(range(m),k):
                MC=marginal_matrix(X,[C]); p=MC@null;r=MC@alt
                nz=p>0; D=float(np.sum(p[nz]*np.log(p[nz]/r[nz])))
                expected=-math.log(.9) if set(C)&B and set(C)-B else 0
                kl_errors.append(abs(D-expected))
results['raw_context_KL']={'cases':len(kl_errors),'max_error':max(kl_errors)}
# Data-sensitive singleton ambiguity: biased marginals change maximum incoherence.
biased=[]
for m in range(2,8):
    X=cube(m); A=marginal_matrix(X,[(i,) for i in range(m)])
    bad=1-np.all(X==X[:,0,None],axis=1).astype(float)
    for alpha in (0,.01,.1,.25,.5,.75,.9,.99,1):
        q=np.zeros(2**m);q[np.all(X==1,axis=1)]=alpha;q[np.all(X==-1,axis=1)]=1-alpha
        bd=bounds(A,A@q,bad); expected=min(1,m*min(alpha,1-alpha))
        assert np.allclose(bd,[0,expected])
        biased.append({'m':m,'alpha':alpha,'max_incoherence':bd[1]})
results['singleton_bias_bounds']=biased
(HERE/'world_checks_results.json').write_text(json.dumps(results,indent=2)+'\n')
print('ADDITIONAL CHECKS:',json.dumps({'complete_context_lp_cases':len(lp_checks),'KL_cases':len(kl_errors),'KL_max_error':max(kl_errors),'biased_cases':len(biased)}))
