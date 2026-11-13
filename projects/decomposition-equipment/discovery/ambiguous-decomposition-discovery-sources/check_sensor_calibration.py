#!/usr/bin/env python3
"""Reproduce algebraic calibration identities; NOT a binary-process simulation.
The positive-definite covariance fixtures have valid diagonal variances but are
not asserted to be jointly realizable by binary spins. The all-size theorem
rests on its proof, not these finite matrix checks.
"""
import json
from pathlib import Path
import numpy as np

rng = np.random.default_rng(20261028)
results = []
for n in [3, 4, 7, 16, 64]:
    P = np.roll(np.eye(n), 1, axis=0)
    A = .35 * P + .15 * P @ P
    R = rng.normal(size=(n, n))
    C = R @ R.T + n * np.eye(n)
    C = C / np.sqrt(np.outer(np.diag(C), np.diag(C)))
    mu = rng.uniform(-.7, .7, n)
    C = C * np.sqrt(np.outer(1-mu**2, 1-mu**2))
    rho = rng.uniform(.3, .9, n)
    D = np.diag(rho)
    a = D @ mu
    G1 = D @ A @ C @ D
    G2 = D @ A @ A @ C @ D
    B = G2 @ np.linalg.inv(G1)
    S = np.linalg.solve(B, G1)
    rh = np.sqrt(np.diag(S) + a*a)
    Di = np.diag(1/rh)
    result = {
        'N': n,
        'rho_error': float(np.max(abs(rh-rho))),
        'A_error': float(np.max(abs(Di @ B @ np.diag(rh)-A))),
        'C_error': float(np.max(abs(Di @ S @ Di-C))),
    }
    assert max(v for k, v in result.items() if k != 'N') < 1e-12
    results.append(result)
report = {
    'scope': 'Algebraic matrix identity check only; C matrices not asserted binary-spin realizable. All-size proof in section 9.',
    'results': results,
}
path = Path(__file__).resolve().parent / 'Sensor_Calibration_QA.json'
path.write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
