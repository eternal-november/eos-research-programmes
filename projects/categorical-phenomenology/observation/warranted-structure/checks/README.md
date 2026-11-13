# Exact executable checks

These programs use only the Python 3 standard library. Python 3.10 or later is
required (`int.bit_count` is used). They use integers, finite sets and tuples, no
floating-point arithmetic, external packages, network requests, or random seeds.

From the enclosing deliverable directory, run:

```sh
python3 checks/run_checks.py --verify checks/results.json
python3 -O checks/run_checks.py --verify checks/results.json
```

Both commands recompute every check and compare the entire deterministic JSON
result byte-for-byte with the supplied snapshot. A failed condition raises an
exception and exits unsuccessfully. The checks remain active under `python -O`.
Running without arguments prints the computed JSON. To deliberately regenerate
the snapshot after reviewing a source change, use:

```sh
python3 checks/run_checks.py --write checks/results.json
```

No timestamps, platform details, or unordered set iterations enter the snapshot.
The empty word is encoded as the empty string, and absence of a meet is `null`.

## What is checked

### Finite orders and universal operations

- The explicit worlds A, B and C from `../alternative.md` are genuine partial
  orders. All positive and negative comparisons on the old names agree.
  Their respective meets of a and b are z, w and absent.
- The comparable pair z≤a has meet z in each world.
- Every labelled poset on 1, 2, 3 or 4 elements is enumerated (counts 1, 3, 19,
  219). The new-meet extension is checked for all 544 incomparable pairs.
  It replaces 123 existing meets and supplies 421 previously absent meets.
- Comparable meets are checked in those constructed extensions and separately
  in every order on four points, using the first three as the old domain.
- Every bipartite graph with n≤3 vertices on each side is converted to the
  three-level poset. Existence of every binary meet is checked directly against
  absence of a four-cycle. Every resulting total meet table is tested for
  idempotence, commutativity and associativity.
- For every negative-answer transcript at n≤3, every compatible graph completion
  is checked. This tests the finite certificate criterion directly, rather than
  assuming that criterion while computing the optimum.
- Four-cycle-free graphs are enumerated for n≤4. The extremal edge counts are
  1, 3, 6, 9, and hence the claimed empty-input certificate sizes are 0, 1, 3, 7.
  At n=4 the independent all-poset/all-completion cross-check is not run; the
  snapshot explicitly records zeros for those unchecked stages.
- For n≤4 every singleton-edge alternative is checked as a witness that an
  unqueried edge can change the full meet table while preserving all meets.

### S3 observations and descent

- Permutations use `(p*q)(i)=p(q(i))`; a word is read by right multiplication.
  The generators are a=(12), b=(123), and the accepting element is the identity.
- The six H words give all group elements and a minimal six-state automaton.
- Finite-depth quotients have 2, 4, 6 classes at depths 0, 1, 2. Every letter's
  descent is tested by all pairs within each class. Explicit failure witnesses
  are recorded at depths 0 and 1, and both letters descend at depth 2.
- All interlevel maps Q_(k+1)→Q_k are checked for well-definedness; constancy on
  restriction fibers agrees with the independent same-level descent test.
- The H state-cover/characterization certificate has exactly 48 distinct query
  words and maximum length five. Its six rows are distinct and all transitions
  are recovered from those rows. The six-state upper bound remains an explicit
  model promise, not a conclusion of this computation.
- The generated transition monoid has six elements, all are bijections, and the
  two generating transformations do not commute. The concrete outputs are
  f(abab)=1 and f(baab)=0.

### Finite length and delayed failure

- For each cutoff L=0,...,6, the truncated behavior agrees with f on every word
  through L. The reachable machine is minimized. A word of length L+1 acts as a
  constant map to its rejecting state, and the minimal machine has at least two
  states, so this transformation is not a bijection. A beyond-horizon
  distinguishing word is recorded.
- All labelled binary-output machines with one or two states are compared in
  pairs by an independent product-state breadth-first search. The shortest
  distinguishing length never exceeds r+s−2; equality occurs in each tested
  state-size combination.
- The unary sharpness family from `../structure.md` is tested for N=2,...,20.
  Both machines are minimal with N states; their first disagreement is at
  length 2N−2. The cycle generator is bijective; the tail-cycle generator
  identifies states 0 and N−1 and is not bijective. The helper internally
  duplicates the unary transition in two
  columns, which does not affect minimization or the effective unary behavior.

## Limits

These are reproducible sanity checks for explicit finite examples and bounded
families. They are not proofs for arbitrary posets, graphs, state bounds or
horizons. They do not establish any empirical model promise, noisy-data result,
algorithmic efficiency claim, or novelty. The general statements require the
separate mathematical arguments and prior-art assessment.
