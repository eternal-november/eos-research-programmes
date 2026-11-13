#!/usr/bin/env python3
"""Independent exact arithmetic and dense checks; no candidate code imported."""
from fractions import Fraction as F
from math import lcm
from itertools import product
import json
import numpy as np

def rotate(x,n,k=1):
    k %= n
    return ((x << k) | (x >> (n-k))) & ((1<<n)-1) if k else x

def coefficients(n):
    # Independently solve UB=A in the cyclic group algebra: u[k]+2u[k+1]=a[k].
    m = [[F(int(i==j)+2*int(j==(i+1)%n)) for j in range(n)] + [F(int(i==0)+2*int(i==1))] for i in range(n)]
    for j in range(n):
        pivot = next(i for i in range(j,n) if m[i][j])
        m[j],m[pivot] = m[pivot],m[j]
        q=m[j][j]; m[j]=[v/q for v in m[j]]
        for i in range(n):
            if i!=j:
                q=m[i][j]; m[i]=[a-q*b for a,b in zip(m[i],m[j])]
    return [r[-1] for r in m]

def exact_moments(n):
    u=coefficients(n); den=lcm(*(v.denominator for v in u)); nums=[int(v*den) for v in u]
    norm=0; singles=[0]*n; pairs=[0]*n
    for x in range(1<<n):
        outputs={}
        for k,c in enumerate(nums):
            y=rotate(x,n,k); outputs[y]=outputs.get(y,0)+c
        for y,c in outputs.items():
            w=c*c; norm+=w
            qs=[1-2*(((x>>j)^(y>>((j+1)%n)))&1) for j in range(n)]
            for j in range(n):
                singles[j]+=w*qs[j]; pairs[j]+=w*qs[0]*qs[j]
    scale=(1<<n)*den*den
    one=[F(s,scale) for s in singles]; pair=[F(s,scale) for s in pairs]
    covariance=[pair[j]-one[0]*one[j] for j in range(1,n)]
    claimed=F(2**(n-1)+2,2**n+1)**2
    return dict(n=n,u1=str(u[1]),unit_circle_parseval=sum(v*v for v in u)==1,coefficient_sum_one=sum(u)==1,choi_norm_one=norm==scale,all_singles_equal_claim=all(v==claimed for v in one),all_pair_moments_equal_claim=all(v==claimed for v in pair[1:]),covariance_min=str(min(covariance)),covariance_max=str(max(covariance)),covariance_at_least_3_over_16=all(v>=F(3,16) for v in covariance))

def dense_checks(n):
    d=1<<n; S=np.zeros((d,d))
    for x in range(d): S[rotate(x,n),x]=1
    A=np.eye(d)+2*S; B=A.T
    U=A@np.linalg.inv(B)
    # Since |M>> has amplitude M[y,x], partial E trace is (M^dagger M)^T.
    marginal_a=(A.T@A).T/np.linalg.norm(A,'fro')**2
    marginal_b=(B.T@B).T/np.linalg.norm(B,'fro')**2
    polynomial=sum(float(c)*np.linalg.matrix_power(S,k) for k,c in enumerate(coefficients(n)))
    return dict(n=n,marginal_equality_max_abs=float(np.max(np.abs(marginal_a-marginal_b))),unitarity_max_abs=float(np.max(np.abs(U.T@U-np.eye(d)))),conversion_max_abs=float(np.max(np.abs(U@B-A))),polynomial_conversion_max_abs=float(np.max(np.abs(polynomial-U))),frobenius_squared=float(np.linalg.norm(B,'fro')**2),frobenius_squared_claim=5*d+8,singular_min=float(np.linalg.svd(B,compute_uv=False).min()))

def tensor_checks(n):
    d=1<<n; bad=good=0; left=right=0
    for x,y in product(range(d),repeat=2):
        old=np.eye(2); new=np.eye(2)
        for j in range(n):
            i=(x>>j)&1; a=(y>>j)&1
            w=np.zeros((2,2)); w[i,a]=1
            old=old@w; new=new@w.T
        old=int(np.trace(old)); new=int(np.trace(new))
        left+=old!=int(y==rotate(x,n,-1)); right+=new!=int(y==rotate(x,n,1))
        # Direct sums contract sectorwise, so total is delta_x,y + 2*trace(W product).
        good+=int(x==y)+2*new != int(x==y)+2*int(y==rotate(x,n))
        bad+=int(x==y)+2*old != int(x==y)+2*int(y==rotate(x,n))
    return dict(n=n,displayed_W_left_shift_mismatches=left,transposed_W_right_shift_mismatches=right,corrected_bond5_A_mismatches=good,displayed_bond5_A_mismatches=bad)

out={'exact_moments':[exact_moments(n) for n in [3,5,7,9,11,13]],'dense':[dense_checks(n) for n in [3,5,7]],'tensor':[tensor_checks(n) for n in [3,4]],'note':'n=9 deliberately tests that the exact prime-size formula should not be silently generalized.'}
print(json.dumps(out,indent=2))
