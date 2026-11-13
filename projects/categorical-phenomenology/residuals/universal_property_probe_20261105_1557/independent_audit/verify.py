#!/usr/bin/env python3
"""Independent exact and numerical checks. Run: python verify.py."""
import json
from pathlib import Path
import numpy as np
import sympy as s
from scipy.linalg import expm


def factors_step(A, B, E, eta):
    return A - eta * E * B.T, B - eta * A.T * E


def cross(H, m):
    return H[:m, m:]


def boost(E):
    m, n = E.shape
    return s.BlockMatrix([[s.zeros(m), E], [E.T, s.zeros(n)]]).as_explicit()


def symmetric_basis(N):
    basis = []
    for i in range(N):
        for j in range(i, N):
            B = s.zeros(N)
            B[i, j] = B[j, i] = 1
            basis.append(B)
    return basis


def observation_rows(basis, M, m):
    outputs = [list(cross(M * B * M.T, m)) for B in basis]
    return s.Matrix(outputs).T


def exact_observation_ranks(m, n):
    N = m + n
    basis = symmetric_basis(N)
    I = s.eye(N)
    units = []
    for i in range(m):
        for j in range(n):
            E = s.zeros(m, n)
            E[i, j] = 1
            units.append(E)
    # eta=1/3 avoids incidental singular congruences. Proof handles all eta!=0.
    maps = [I - s.Rational(1, 3) * boost(E) for E in units]
    O0 = observation_rows(basis, I, m)
    O1 = O0.col_join(s.Matrix.vstack(*[observation_rows(basis, M, m) for M in maps]))
    O2 = O1.col_join(s.Matrix.vstack(*[
        observation_rows(basis, M2 * M1, m) for M1 in maps for M2 in maps
    ]))
    D = N * (N + 1) // 2
    r1, r2 = O1.rank(), O2.rank()
    assert r1 == D - 1
    assert r2 == D - (m == n == 1)
    return dict(m=m, n=n, state_dimension=D, one_step_rank=r1, two_step_rank=r2)


def example_symbolic():
    eta = s.symbols("eta", nonzero=True)
    A1, B1 = s.Matrix([[1]]), s.Matrix([[0, 0]])
    A2, B2 = s.Matrix([[0, 0]]), s.eye(2)
    E, Z = s.Matrix([[1, 0]]), s.Matrix([[0, 1]])
    A1, B1 = factors_step(A1, B1, E, eta)
    A2, B2 = factors_step(A2, B2, E, eta)
    F1 = s.simplify(A1 * B1)
    assert s.simplify(F1 - A2 * B2) == s.zeros(1, 2)
    A1, B1 = factors_step(A1, B1, Z, eta)
    A2, B2 = factors_step(A2, B2, Z, eta)
    d = s.simplify(A1 * B1 - A2 * B2)
    assert d == s.Matrix([[0, eta**3]])
    return dict(F1=str(F1), F2_difference=str(d),
                first_target="(-1,0)", second_target="(-eta,-1)")


def scalar_symbolic():
    p, q, f, e, eta = s.symbols("p q f e eta")
    H = s.Matrix([[p, f], [f, q]])
    M = s.eye(2) - eta * boost(s.Matrix([[e]]))
    Hp = s.expand(M * H * M)
    assert s.simplify(Hp[0, 1] - ((1 + eta**2 * e**2) * f - eta * e * (p + q))) == 0
    assert s.simplify(s.trace(Hp) - ((1 + eta**2 * e**2) * (p + q) - 4 * eta * e * f)) == 0
    return "Scalar dynamics close exactly on (f,p+q)."


def numerical_checks():
    rng = np.random.default_rng(1729)
    max_update_error = 0.0
    max_flow_shift_error = 0.0
    max_fixed_target_error = 0.0
    for m, n in [(1, 2), (2, 1), (2, 3), (3, 3)]:
        N = m + n
        J = np.diag([1.] * m + [-1.] * n)
        C = rng.normal(size=(N, N + 2))
        H = C @ C.T
        E = rng.normal(size=(m, n))
        S = np.block([[np.zeros((m, m)), E], [E.T, np.zeros((n, n))]])
        eta = .021
        A, B = C[:m], C[m:].T
        Anew, Bnew = A - eta * E @ B.T, B - eta * A.T @ E
        Cnew = np.concatenate([Anew, Bnew.T])
        M = np.eye(N) - eta * S
        err = np.linalg.norm(Cnew @ Cnew.T - M @ H @ M)
        max_update_error = max(max_update_error, float(err))
        T = expm(-.37 * S)
        err = np.linalg.norm(T @ J @ T.T - J)
        max_flow_shift_error = max(max_flow_shift_error, float(err))
        # Distinct shifted initial Gram states, same output for every fixed Y.
        H1 = np.diag([1.] * m + [0.] * n)
        H2 = np.diag([0.] * m + [1.] * n)
        Y = rng.normal(size=(m, n))
        for _ in range(120):
            max_fixed_target_error = max(max_fixed_target_error, float(np.linalg.norm(H1[:m, m:] - H2[:m, m:])))
            for Hcur in (H1, H2):
                Ecur = Hcur[:m, m:] - Y
                Scur = np.block([[np.zeros((m, m)), Ecur], [Ecur.T, np.zeros((n, n))]])
                Mcur = np.eye(N) - eta * Scur
                Hcur[:] = Mcur @ Hcur @ Mcur
    assert max_update_error < 1e-11
    assert max_flow_shift_error < 1e-11
    assert max_fixed_target_error < 1e-11
    return dict(max_update_error=max_update_error,
                max_flow_shift_error=max_flow_shift_error,
                max_fixed_target_error=max_fixed_target_error)


result = dict(
    example=example_symbolic(),
    scalar=scalar_symbolic(),
    exact_ranks=[exact_observation_ranks(m, n) for m in range(1, 4) for n in range(1, 4)],
    numerical=numerical_checks(),
    qualification="Finite tests verify identities and examples; the accompanying proof handles arbitrary dimensions and nonzero stepsizes."
)
Path(__file__).with_name("results.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
