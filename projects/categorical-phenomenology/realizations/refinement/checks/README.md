# Exact finite verification of the partition refinement family

Run with Python 3; no third-party dependencies:

```sh
python3 verify_partition_refinements.py > actual.json
cmp actual.json expected_results.json
python3 -O verify_partition_refinements.py > optimized.json
cmp optimized.json expected_results.json
```

All arithmetic uses `fractions.Fraction`; checks use explicit exceptions rather than `assert`, so optimization does not disable them. The fixed roster comprises every ordered pair (B,D) of partitions of n symbols for 1 <= n <= 5, at uniform probabilities and at p_i=(i+1)/(n(n+1)/2), with the duplicate n=1 vector omitted.

| n | partitions | probability vectors | cases | feasible | obstructed |
|---|---:|---:|---:|---:|---:|
| 1 | 1 | 1 | 1 | 1 | 0 |
| 2 | 2 | 2 | 8 | 6 | 2 |
| 3 | 5 | 2 | 50 | 24 | 26 |
| 4 | 15 | 2 | 450 | 120 | 330 |
| 5 | 52 | 2 | 5408 | 716 | 4692 |
| total | | | 5917 | 867 | 5050 |

The source constructs the chosen coarse generator from B and the requested fine behavior from D. For each feasible case it constructs both comparison choices explicitly. It checks nonnegative normalized joint output/next-state kernels, normalized stochastic links (point-valued for deterministic comparisons), initial-law preservation, and every coarse output's matrix intertwining equation. It checks all first/second-output word probabilities and that all post-second mass resides in the absorbing #-state. Combined with stochasticity, that proves the specified full phase-word law for each constructed witness, not just a selected finite prefix sample. State counts include root and terminal: |D|+2 and |B|+2. There are 718 cases with a strict gap between these constructed costs.

For each infeasible case it finds a positive-mass B-block that crosses D-blocks, verifies that every possible fine first report excludes it from the linked posterior's support, and verifies positive missing mass in the required coarse posterior. The accompanying mathematical proof explains why this certificate rules out *any* state count; the program does not search all latent realizations or prove the lower-bound theorem. The lower bounds and if-and-only-if theorem are in the report/`partition_theorem.md`.

Explicit extra controls are the two-symbol delayed-coin obstruction, early-coin full revelation, and the stochastic/deterministic cost distinction without first-step revelation. These four controls are additional checks, not extra roster cases.

Scope: finite, time-homogeneous generators, one action, strictly positive probabilities, strong statewise joint-output/next-state links. This is not a test of approximate links, zero probabilities, controlled policies, or arbitrary latent minimization. A deterministic projection and a stochastic link impose different preservation requirements.

`reproduction_receipt.json` records fresh-copy normal and optimized executions and SHA-256 hashes. It is an execution receipt, not formal proof certification.

The same 867 positive cases also check the two-stage polytope bridge: K[D,B]=p(B) for B contained in D, Q[B,i]=p_i/p(B) for i in B, and R[D,i]=p_i for i in D. The checker verifies KQ=R, prescribed column masses p(B), row masses p(D), pairwise disjoint nonempty row supports, and the factorization I K. The support certificate gives ordinary rank |D|; together with I K this certifies nonnegative rank |D|. The negative crossing-block certificate also excludes feasible K by positivity (see the proof); no LP solver is used. These checks do not add new roster cases.

Three separately counted binary noisy-channel controls go beyond support obstructions. For Q=[[4/5,1/5],[1/5,4/5]] and column masses (1/2,1/2), the checker verifies an exact two-sided inverse and hence uniqueness K=R Q^-1. Independent R (all entries 1/4) has nonnegative rank one K, giving three stochastic versus four deterministic states. Intermediate R (diagonal 37/100, off-diagonal 13/100) has K with diagonal 9/20 and off-diagonal 1/20, of nonnegative rank two, giving four states in either comparison mode. Sharper R (diagonal 9/20, off-diagonal 1/20) has the unique signed K with diagonal 7/12 and off-diagonal -1/12, so is infeasible although R and Q both have full support. Matrix equations, both marginals, positivity conditions, ordinary rank and nonnegative factorization witnesses are checked exactly. Resource conclusions invoke the accompanying two-stage theorem. These three controls do not change the 5,917 partition cases.
