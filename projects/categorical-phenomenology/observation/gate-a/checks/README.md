# Independent exact Gate A checks

These are **finite reproducibility checks, not proofs or novelty clearance**. They independently implement the displayed matrix operations and examples with Python's standard library. No SymPy, NumPy, packages, network, floating-point arithmetic, randomness, or `assert` statements are used.

## Run

From the checks directory, using Python 3.8 or later:

```sh
python3 run_all.py
```

For a copied bundle, use `python3 run_all.py` in its directory. The runner executes `exact_checks.py` normally and with `-O`, compares the complete JSON outputs byte-for-byte, and tests that deliberate failures exit 1 in both modes. It writes `results.json`, `results_optimized.json`, `verification.json`, and `manifest.json` with SHA-256 content hashes.

Individual run:

```sh
python3 exact_checks.py --output results.json
python3 -O exact_checks.py --output results_optimized.json
python3 -O exact_checks.py --self-test-failure
```

The last command is an intentional negative control and must fail with exit status 1.

## What is checked

- **54 exact observation-closure cases.** Paths on 2–8 vertices (all regimes through 6, jets through 8), stars on 3–6, even cycles on 4 and 6, K(2,3), and a disconnected path-plus-edge-plus-isolate. Connected flow/jet dimension is d(d+1)/2−1. GD dimension is d(d+1)/2 for d≥3 and 2 for d=2. The fixed GD step is 1/3; the two-step case uses 1/3 and 2/3. The base step 1/3 satisfies the two-size theorem’s eta<1/2 condition.
- **Sharp path jet depth on the tested sizes.** Both the closure basis depth and first nonzero far-end diagonal coefficient are 2d−3. Endpoint basis words satisfy the stated dimension-minus-one bound.
- **Fixed-step recovery of the infinitesimal operator.** Lagrange interpolation is evaluated exactly on all six symmetric 3×3 basis matrices, for eta = 1/5, 1/3, 1/2, 2/3, 4/5. Two-size polarization identities are independently checked. Fixed-duration flow at log 2 is rational, preserves J exactly, and its five-node interpolation recovers the infinitesimal operator.
- **Native star examples for d=3–12.** I and I+J=diag(2,0,…,0) have ranks d and 1, lie on the same signed-diagonal pencil, and the thin law is nonzero. A sensor-specific GD discriminator is checked. These are examples of a native-width contrast, not a general minimal-realization algorithm.
- **The d=2 exception is explicit.** I2 and diag(2,0) have different Gram ranks but identical flow and GD responses. Their response-minimum width is 1 in both regimes. Thus the GD minimum-width-equals-rank statement must be restricted to the full-Gram-identifiable d≥3 case.
- **HMM normalization and exact finite-prefix growth.** For m=1,2,3,4 prime controls, the actual normalized belief orbits through n=8 have binomial(n+m,m) states. All outcomes, including resets, are included; each control's sum is row-stochastic. Prime valuation ranks equal m. The finite example has exactly four eventual beliefs. The no-reset mixture has n+1 states at exactly time n but binomial(n+2,2) through time n, checked through n=10. A boundary-seed control has one state, demonstrating why full support matters. The supplied nonperfect terminal tests include their complements and are normalized. Operator reconstruction from the invertible preparation response block is checked exactly.

## Diagnostic counterexample, not a passing theorem claim

The bundle records `DISPLAYED_HYPOTHESES_GAP_CONFIRMED` for the comparative construction if its terminal-event list omits complements and no upper-bound check is imposed:

- Preparations: (2/5,3/5), (3/5,2/5).
- Terminal effects: (3/2,0), (0,3/2), belonging to separate binary tests.
- Only dynamic event: I.
- Observed terminal table: [[3/5,9/10],[9/10,3/5]], valid and rank 2.
- Positivity of only these two effects yields the standard simplex, at whose vertices an effect equals 3/2.

Thus the displayed simplex is not a probabilistic realization of all terminal effects. Include complementary terminal outcomes in the cone, or require ell_t≤u on the computed cone and normalization within each test. Including complements in this example yields interval vertices with first coordinates 1/3 and 2/3, and all terminal probabilities are then valid. This counterexample targets the displayed construction, not existence of some positive realization.

## Implementation boundaries

Closure uses breadth-first words and rational Gaussian elimination. Integer scaling of each generated observable is removed by its gcd, so dimensions and word depths are exact while coefficient growth stays small. These scaled matrices are used only for span checks; they are not reported as unscaled experimental measurements. The implementation does not import or execute the earlier SymPy checker. The arithmetic-rank code checks rational diagonal examples; it is not a complete Reidemeister–Schreier implementation for arbitrary monomial groups.

No finite sample proves the graph theorem for all graphs, proves asymptotic HMM growth, establishes generic formation during training, checks robustness to noise, or establishes novelty. The parent report must keep those claims separate.
