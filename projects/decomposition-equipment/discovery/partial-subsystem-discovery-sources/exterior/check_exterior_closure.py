"""Small exact-law numerical checks; not an experimental or physical audit."""
from pathlib import Path
from collections import defaultdict
from itertools import product
import json
import numpy as np


def tv(p, q):
    return float(np.abs(np.asarray(p) - np.asarray(q)).sum() / 2)


def tilt_matrix(theta, scores, weights):
    a = np.exp(np.outer(theta, scores)) * weights[None, :]
    return a / a.sum(axis=1, keepdims=True)


def feedback_law(horizon, error, exterior_kind):
    # x is private local state; z is an unobserved persistent exterior mode.
    # a_t depends only on the previous visible output. u_t arrives before
    # local sampling. v_t is a noisy reading, not the local state itself.
    states = {(0, 0, 0, ()): .5, (1, 1, 0, ()): .5}
    for _ in range(horizon):
        nxt = defaultdict(float)
        for (x, z, old_v, hist), mass in states.items():
            a = old_v
            p_u = .15 + .25*z + .15*a + .10*old_v
            for u in (0, 1):
                pu = p_u if u else 1-p_u
                p_x = .18 + .14*x + .13*u + .08*a + .07*x*u
                p_x += error * (2*z-1)
                assert 0 < p_x < 1
                for xp in (0, 1):
                    px = p_x if xp else 1-p_x
                    for v in (0, 1):
                        pv = .8 if v == xp else .2
                        if exterior_kind == 'persistent':
                            p_z = .12 + .60*z + .10*v
                        else:
                            p_z = .72 - .50*z + .10*v
                        for zp in (0, 1):
                            pz = p_z if zp else 1-p_z
                            nxt[(xp, zp, v, hist+((a,u,v),))] += mass*pu*px*pv*pz
        states = nxt
    law = defaultdict(float)
    for (_, _, _, h), mass in states.items():
        law[h] += mass
    assert abs(sum(law.values())-1) < 1e-12
    return law


def main():
    rng = np.random.default_rng(7331)
    worst = 0.0
    min_singular = 1.0
    for r in range(2, 7):
        theta = np.linspace(-1.2, 1.2, r+1)
        scores = np.linspace(-1, 1, r)
        weights = rng.uniform(.2, 1, r); weights /= weights.sum()
        m = tilt_matrix(theta, scores, weights)
        min_singular = min(min_singular, np.linalg.svd(m, compute_uv=False)[-1])
        assert np.linalg.matrix_rank(m) == r
        left = np.linalg.pinv(m)
        assert np.max(np.abs(left @ m - np.eye(r))) < 1e-8
        k = rng.uniform(.1, 1, (r, 3)); k /= k.sum(axis=1, keepdims=True)
        l = m @ k
        q = l.mean(axis=0)
        actual = max(tv(row,q) for row in k)
        bound = np.abs(left).sum(axis=1).max() * max(tv(row,q) for row in l)
        worst = max(worst, actual-bound)
        assert actual <= bound+1e-10
        fixed = np.tile(np.array([.2,.3,.5]), (r,1))
        assert np.max(np.abs(left@(m@fixed)-fixed)) < 1e-8

    m = np.tile(np.array([.2,.5,.3]), (2,1))
    v = np.array([1,-.4,0])
    assert np.max(np.abs(m@v)) < 1e-15
    p1 = .4 + .1*v
    observed = m@p1
    assert np.max(np.abs(observed-.4)) < 1e-15
    shifted = np.array([.8,.1,.1])@p1
    assert abs(shifted-.4) > .07

    # Regime richness before conditioning can vanish after conditioning.
    conditional = np.array([[.8,.2],[.2,.8]])
    c_laws = np.array([[.8,.2],[.2,.8]])
    unconditional = c_laws@conditional
    assert np.linalg.matrix_rank(unconditional) == 2
    assert np.linalg.matrix_rank(np.tile(conditional[0],(2,1))) == 1

    joint = []
    for rho in (-.6,.6):
        p = np.array([[1+rho,1-rho],[1-rho,1+rho]])/4
        assert np.max(np.abs(p.sum(axis=0)-.5)) < 1e-15
        assert np.max(np.abs(p.sum(axis=1)-.5)) < 1e-15
        joint.append(p)
    joint_gap = tv(joint[0],joint[1])
    assert abs(joint_gap-.6)<1e-15

    traces=[]
    epsilon=.025
    for kind in ('persistent','alternating'):
        for horizon in (1,2,3,4,5):
            p=feedback_law(horizon,epsilon,kind)
            q=feedback_law(horizon,0,kind)
            distance=sum(abs(p.get(h,0)-q.get(h,0)) for h in set(p)|set(q))/2
            assert distance <= horizon*epsilon+1e-12
            traces.append({'exterior':kind,'horizon':horizon,'transcript_tv':distance,
                           'uniform_coupling_bound':horizon*epsilon})
    result={
        'status':'PASS',
        'scope':'Finite exact-law numerical checks; no discovery or finite-data implementation.',
        'soft_tilt_mode_counts_checked':list(range(2,7)),
        'minimum_singular_value_in_tilt_fixtures':float(min_singular),
        'uniform_hidden_effect_bound_max_violation':float(worst),
        'rank_deficient_observed_probability':float(observed[0]),
        'new_exterior_probability':float(shifted),
        'unconditional_mixture_determinant':float(np.linalg.det(unconditional)),
        'conditional_mixture_rank':1,
        'separate_marginals_joint_shift_tv':joint_gap,
        'adaptive_feedback_checks':traces,
    }
    Path(__file__).with_name('Exterior_Closure_QA.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
