"""Exact passive-history example and compact LP certificate checks.

The passive-history check uses Fractions, not a fitted predictor or approximate
comparison. LP checks are bounded numerical regressions, not formal proofs.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json
import numpy as np
from scipy.optimize import linprog


def kernel(theta):
    out = {}
    for a,b in product(range(2), repeat=2):
        p = (F(1,4) if a == 0 else F(3,4)) + theta*(2*b-1)
        out[a,b] = {(aa,bb):(p if aa else 1-p)/2
                    for aa,bb in product(range(2), repeat=2)}
    return out


def observed_word_prob(word, theta):
    k=kernel(theta)
    d={(word[0],b):F(1,4) for b in range(2)}
    for aa in word[1:]:
        nd={(aa,b):F(0) for b in range(2)}
        for x,px in d.items():
            for y in nd: nd[y]+=px*k[x][y]
        d=nd
    return sum(d.values())


def expected_word_prob(word):
    p=F(1,2)
    for a,aa in zip(word,word[1:]):
        t=F(1,4) if a==0 else F(3,4)
        p*=t if aa else 1-t
    return p


def extrema(c, A, b, bounds):
    lo=linprog(c,A_eq=A,b_eq=b,bounds=bounds,method='highs')
    hi=linprog(-np.array(c),A_eq=A,b_eq=b,bounds=bounds,method='highs')
    assert lo.success and hi.success
    return float(lo.fun),float(-hi.fun),lo.x.tolist(),hi.x.tolist()


def main():
    thetas=[F(-1,8),F(0),F(1,8)]
    words=0
    for n in range(1,11):
        for w in product(range(2),repeat=n):
            expected=expected_word_prob(w)
            assert all(observed_word_prob(w,t)==expected for t in thetas)
            words+=1
    mins=[]
    contrast={}
    for t in thetas:
        k=kernel(t); mins.append(min(v for r in k.values() for v in r.values()))
        for r in k.values(): assert sum(r.values())==1
        for a in range(2):
            diff=sum(v for (aa,bb),v in k[a,1].items() if aa==1)-sum(v for (aa,bb),v in k[a,0].items() if aa==1)
            assert diff==2*t
        contrast[str(t)]=str(diff)
    # Coupled constraints preserve sum effects although each summand is unknown.
    A=np.array([[1.,1.]])
    b=np.array([0.])
    bounds=[(-0.1,0.1),(-0.1,0.1)]
    sum_range=extrema([1.,1.],A,b,bounds)
    individual_range=extrema([1.,0.],A,b,bounds)
    assert np.max(np.abs(sum_range[:2]))<1e-12
    assert np.allclose(individual_range[:2],[-.1,.1])
    # The exact dual certificate for c=(1,1) is lambda=1, mu=0.
    assert np.array_equal(A.T@np.array([1.]),np.array([1.,1.]))
    # E=(1,1) does not resolve an individual contrast; E=(1,0) does.
    v=np.array([1.,-1.]); target=np.array([1.,0.])
    E_bad=np.array([[1.,1.]]); E_good=np.array([[1.,0.]])
    assert np.allclose(E_bad@v,0) and not np.allclose(target@v,0)
    assert not np.allclose(E_good@v,0)
    # A boundary-only polytope must use its true affine hull, not ker(A).
    face=linprog([-1.,0.],A_ub=[[1.,1.]],b_ub=[0.],bounds=[(0,None),(0,None)],method='highs')
    assert face.success and abs(face.fun)<1e-12 and np.allclose(face.x,0)
    result={
      'status':'PASS',
      'exact_observed_words':words,
      'maximum_word_length':10,
      'fixed_world_parameters':[str(x) for x in thetas],
      'minimum_transition_probability':str(min(mins)),
      'pointwise_autonomy_intervention_contrasts':contrast,
      'coupled_sum_range':sum_range[:2],
      'individual_unidentified_range':individual_range[:2],
      'coupled_extremizers':individual_range[2:],
      'experiment_nullspace_check':'PASS',
      'forced_face_check':'PASS',
      'scope':'Exact rational passive-history fixture; numerical compact LP regressions; not a discovery algorithm or generic experiment-access promise.'
    }
    p=Path(__file__).with_suffix('.json');p.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
