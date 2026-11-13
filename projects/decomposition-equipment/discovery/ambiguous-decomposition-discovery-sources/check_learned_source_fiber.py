#!/usr/bin/env python3
"""Finite seeded checks of the P111 source-fiber formulas, not a general proof."""
import itertools
import json
from pathlib import Path
import numpy as np

rng = np.random.default_rng(2026)
xs = np.array(list(itertools.product([0, 1], repeat=3)))
errors = []
for trial in range(100):
    p = rng.dirichlet(np.ones(8)*2)
    e = p @ xs
    a, b, c = [p @ (xs[:, i]*xs[:, j]) for i, j in [(0, 1), (0, 2), (1, 2)]]
    t = p[7]
    L = max(0, a+b-e[0], a+c-e[1], b+c-e[2])
    U = min(a, b, c, 1-sum(e)+a+b+c)
    reconstructed = np.array([
        1-sum(e)+a+b+c-t,
        e[2]-b-c+t,
        e[1]-a-c+t,
        c-t,
        e[0]-a-b+t,
        b-t,
        a-t,
        t,
    ])
    errors.append(float(max(abs(reconstructed-p))))
    assert L < t < U
assert max(errors) < 1e-12
report = {
    'random_positive_triples': 100,
    'maximum_reconstruction_error': max(errors),
    'scope': 'Checks learned P111 fiber formulas only; theorem proof covers all positive triples.',
}
path = Path(__file__).resolve().parent / 'Learned_Source_Fiber_QA.json'
path.write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
