#!/usr/bin/env python3
"""Finite regression checks for Positive_Atlas_Gluing.md, not a general proof."""
import itertools
import json
import math
import numpy as np


def bits(n):
    return np.array(list(itertools.product((0, 1), repeat=n)), dtype=int)


def product_mass(states, probs):
    return np.prod(np.where(states, probs, 1 - np.asarray(probs)), axis=1)


def marginal(states, mass, scope):
    out = np.zeros(2 ** len(scope))
    for row, p in zip(states, mass):
        idx = sum(int(row[j]) << (len(scope) - 1 - k) for k, j in enumerate(scope))
        out[idx] += p
    return out


def tv(p, q):
    return float(np.abs(p-q).sum()/2)


def kl(p, q):
    return float(np.dot(p, np.log(p/q)))


def twist(states):
    z=states.copy()
    z[:,0] ^= z[:,1]
    z[:,-1] ^= z[:,-2]
    return z


n=5
X=bits(n)
Y=twist(X)
patches=[(i,i+1) for i in range(n-1)]
eta=0.1
results={}
max_true_product_residual=0.0
max_degenerate_product_residual=0.0
max_bound_slack_violation=0.0
min_twisted_detection=1.0
max_exact_marginal_global_error=0.0
for old in X:
    # Nonlinear feedback includes a Boolean AND and a signed local interaction.
    probs=np.array([0.2+0.15*old[(i-1)%n]+0.2*(old[i]&old[(i+1)%n]) for i in range(n)])
    p=product_mass(X,probs)
    assert abs(p.sum()-1)<1e-12
    # Untwisted factorization exactly glues.
    q=product_mass(X, X.T@p)
    max_true_product_residual=max(max_true_product_residual,tv(p,q))
    # In the twisted atlas, inspect all full pair-patch marginal distributions.
    one=Y.T@p
    qtw=product_mass(Y,one)
    eps=[tv(marginal(Y,p,s),marginal(Y,qtw,s)) for s in patches]
    min_twisted_detection=min(min_twisted_detection,max(eps))
    # Owner of true atoms 0,1 is patch0; atoms 2,3,4 use patches1,2,3.
    owners=[0,0,1,2,3]
    c=sum(eps[i] for i in owners)*math.log(1/eta)
    sym=kl(p,qtw)+kl(qtw,p)
    max_bound_slack_violation=max(max_bound_slack_violation,sym-c,tv(p,qtw)-math.sqrt(c/2))
    # When both end innovations are fair, the complement twists survive.
    deg=probs.copy(); deg[0]=deg[-1]=0.5
    pd=product_mass(X,deg)
    qd=product_mass(Y,Y.T@pd)
    max_degenerate_product_residual=max(max_degenerate_product_residual,tv(pd,qd))
    patch_error=max(tv(marginal(Y,pd,s),marginal(Y,qd,s)) for s in patches)
    if patch_error < 1e-12:
        max_exact_marginal_global_error=max(max_exact_marginal_global_error,tv(pd,qd))
results.update({
    'states_checked':len(X),
    'nonlinear_feedback_old_contexts':len(X),
    'untwisted_product_max_tv':max_true_product_residual,
    'twisted_atlas_min_detecting_patch_tv':min_twisted_detection,
    'degenerate_twist_global_max_tv':max_degenerate_product_residual,
    'exact_local_match_global_max_tv':max_exact_marginal_global_error,
    'quantitative_bound_max_violation':max_bound_slack_violation,
})
assert max_true_product_residual<1e-12
assert min_twisted_detection>0.005
assert max_degenerate_product_residual<1e-12
assert max_bound_slack_violation<1e-12

# Boolean lattice does not imply a Cartesian product.
U=[(0,0),(0,1),(1,0)]
assert len(U)==3 and len(set(a for a,b in U))*len(set(b for a,b in U))==4
results['boolean_but_nonproduct_support_size']=3
results['boolean_but_nonproduct_quotient_product_size']=4

# Three separately valid deterministic quotient matchings with flip holonomy.
valid=[x for x in itertools.product((0,1),repeat=3) if x[0]==x[1] and x[1]==x[2] and x[2]==1-x[0]]
assert valid==[]
results['flip_holonomy_global_assignments']=len(valid)

# Pairwise-full support does not imply full product support.
even=[x for x in itertools.product((0,1),repeat=3) if sum(x)%2==0]
assert all(len({(x[i],x[j]) for x in even})==4 for i,j in itertools.combinations(range(3),2))
results['pairwise_full_parity_support_size']=len(even)
results['pairwise_full_parity_product_size']=8

print(json.dumps(results,indent=2))

# Lagged initialization: positive fresh kernels but deterministic shift zeros.
S=bits(4)  # first two are current, last two previous
lookup={tuple(s):j for j,s in enumerate(S)}
P=np.zeros((16,16)); Q=np.zeros((16,16))
for j,h in enumerate(S):
    pp=np.array([0.3+0.10*h[0]+0.05*h[3],0.25+0.10*h[1]+0.05*h[2]])
    qq=pp+0.01
    for z,pm,qm in zip(bits(2),product_mass(bits(2),pp),product_mass(bits(2),qq)):
        k=lookup[tuple(np.r_[z,h[:2]])]
        P[j,k]=pm; Q[j,k]=qm
beta=max(tv(P[j],Q[j]) for j in range(16))
pi=np.ones(16)/16
for _ in range(500): pi=pi@P
q=np.zeros(16); q[0]=1
lag_viol=0.0
for T in range(1,13):
    q=q@Q
    bound=T*beta+4*(0.15**(T//2))
    lag_viol=max(lag_viol,tv(pi,q)-bound)
assert lag_viol<1e-12
print(json.dumps({'lag2_states':16,'fresh_row_beta':beta,'lag2_burnin_max_violation':lag_viol,'shift_kernel_zero_count':int(np.sum(P==0))},indent=2))


def refine_partition(kernels, labels):
    labels=np.asarray(labels)
    history=[len(set(labels))]
    while True:
        blocks=sorted(set(labels))
        keys=[]
        for row in range(len(labels)):
            key=[int(labels[row])]
            for mat in kernels:
                key.extend(round(float(mat[row,labels==b].sum()),12) for b in blocks)
            keys.append(tuple(key))
        unique={k:j for j,k in enumerate(sorted(set(keys)))}
        nxt=np.array([unique[k] for k in keys])
        history.append(len(unique))
        if len(unique)==len(blocks): return nxt,history
        labels=nxt

# An instantaneous outgoing bit requires recursive memory of one extra bit,
# but a third hidden bit is irrelevant. Controlled strong lumpability.
T=bits(3)  # r,m,n
controlled=[]
for u in (0,1):
    K=np.zeros((8,8))
    for i,(r,m,n0) in enumerate(T):
        ps=[0.1+0.2*r+0.4*m+0.1*u,0.2+0.5*r,0.3+0.2*n0]
        K[i]=product_mass(T,ps)
    controlled.append(K)
labels, stages=refine_partition(controlled,T[:,0])
assert len(set(labels))==4
assert stages==[2,4,4]
for i,j in itertools.product(range(8),repeat=2):
    assert (labels[i]==labels[j]) == bool(np.array_equal(T[i,:2],T[j,:2]))

# Overlapping readout summaries: each is an iid fair bit, but jointly needs Z.
# R,H,Z shared; A and B are separate private irrelevant coordinates.
V=bits(5)
K=np.zeros((32,32))
for i,(r,h,z,a,b) in enumerate(V):
    ps=[0.5,0.2+0.6*z,0.2+0.6*z,0.25+0.2*a,0.35+0.2*b]
    K[i]=product_mass(V,ps)
qS=V[:,0]; qT=V[:,0]^V[:,1]
_,s_stages=refine_partition([K],qS)
_,t_stages=refine_partition([K],qT)
qpair=2*qS+qT
joint,j_stages=refine_partition([K],qpair)
assert s_stages==[2,2] and t_stages==[2,2]
assert j_stages==[4,8,8]
for i,j in itertools.product(range(32),repeat=2):
    assert (joint[i]==joint[j]) == bool(np.array_equal(V[i,:3],V[j,:3]))
# Same old summary, distinct old Z causes exactly 0.6 TV in next pair law.
r0=np.where((V==[0,0,0,0,0]).all(axis=1))[0][0]
r1=np.where((V==[0,0,1,0,0]).all(axis=1))[0][0]
p0=np.array([K[r0,qpair==a].sum() for a in range(4)])
p1=np.array([K[r1,qpair==a].sum() for a in range(4)])
assert abs(tv(p0,p1)-0.6)<1e-12
print(json.dumps({
 'recursive_interface_partition_sizes':stages,
 'crossing_left_partition_sizes':s_stages,
 'crossing_right_partition_sizes':t_stages,
 'crossing_joint_repair_partition_sizes':j_stages,
 'crossing_same_summary_next_joint_tv':tv(p0,p1),
 'crossing_fresh_kernel_min_entry':float(K.min()),
},indent=2))
