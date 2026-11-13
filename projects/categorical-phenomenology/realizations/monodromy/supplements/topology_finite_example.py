"""Numerical smoke test of the finite certificate, not interval arithmetic.

The certifier sees sampled matrices and declared geometry/modulus, not the
continuum generating formula. Replace numerical inequalities by certified
interval computations for a machine-checkable proof under rounding error.
"""
import json
import numpy as np

N, p, m = 64, 3, 3
beta = 0.05
h = np.pi / N
L_true = beta
L_candidate = 0.2
noise_bound = 0.0
vertex_fit = 0.0
basis = np.array([[1, 1], [-1, 1], [0, -2]], dtype=float)
basis[:, 0] /= np.sqrt(2)
basis[:, 1] /= np.sqrt(6)
c = np.ones(m) / m

# Experimental sample generation. Everything below uses only these tables.
tables = []
for theta in np.arange(N) * h:
    u = basis @ np.array([np.cos(theta), np.sin(theta)])
    P = np.outer(u, u)
    tables.append(np.vstack([c, c + beta * P @ basis[:, 0],
                             c + beta * P @ basis[:, 1]]))
tables = np.array(tables)
assert np.max(np.abs(tables.sum(axis=2) - 1)) < 1e-14
assert np.min(tables) > 0

C = np.array([[-1., 1., 0.], [-1., 0., 1.]])
B = np.array([C @ H for H in tables])
G = np.array([b.T @ b for b in B])
values, frames = np.linalg.eigh(G)
gaps = values[:, -1] - values[:, -2]
Q = frames[:, :, -1:]
xi = np.sqrt(p) * (noise_bound + L_true * h)
q = np.array([(2 * np.linalg.norm(b, 2) + xi) * xi for b in B])
signal = np.sqrt(np.min(values[:, -1] - q))
projector_bound = np.max(q / (gaps - q))
signs = []
for v in range(N):
    w = (v + 1) % N
    overlap = np.linalg.det(Q[v].T @ Q[w])
    assert abs(overlap) > 0.99
    signs.append(int(overlap < 0))
parity = sum(signs) % 2
candidate_margin = np.sqrt(p) * (
    vertex_fit + noise_bound + (L_true + L_candidate) * h)
assert np.all(q < gaps / 4)
assert parity == 1
assert candidate_margin < signal

# Entirely data-interpolant version, requiring no truth modulus.
dv = np.array([max(np.linalg.norm(B[(v-1)%N]-B[v], 2),
                  np.linalg.norm(B[(v+1)%N]-B[v], 2)) for v in range(N)])
qbar = np.array([(2*np.linalg.norm(B[v], 2)+dv[v])*dv[v] for v in range(N)])
sbar = np.sqrt(np.min(values[:, -1]-qbar))
assert np.all(qbar < gaps/4)
assert np.sqrt(p)*(vertex_fit+L_candidate*h) < sbar

print(json.dumps({
    'vertices': N,
    'mesh': h,
    'min_table_entry': float(tables.min()),
    'min_spectral_gap': float(gaps.min()),
    'max_certified_covariance_error': float(q.max()),
    'max_projector_error_bound': float(projector_bound),
    'orientation_cycle_parity': parity,
    'signal_lower_bound': float(signal),
    'candidate_error_upper_bound': float(candidate_margin),
    'candidate_Lipschitz_bound': L_candidate,
    'certified_normalized_state_lower_bound': 3,
    'data_interpolant_signal_lower_bound': float(sbar),
    'warning': 'Floating-point smoke test, not an interval-arithmetic proof.'
}, indent=2))
