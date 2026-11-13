# Interface changes and fixed budget optimization

This study tests how the finite native realization problem behaves under a supplied lawful change of interface, and which parts extend to its fixed-budget quartic encoding.

## Main deliverable

- `report.tex` is the complete technical note. It does not depend on LaTeX fragments or external data files.
- `exact_transport_checks.py` contains dependency-free exact rational regression checks, including independent sparse-polynomial differentiation of the actual residual objective.
- `run_exact_checks.sh` runs the mathematical checks in ordinary and optimized Python, verifies byte-identical reports, and compares them with `exact_transport_expected.txt`.
- `check_tex_source.py` performs limited static TeX checks for balanced braces/environments, duplicate labels, unresolved references, and missing bibliography keys.
- `source_checks.json` records the static check result.
- `Review.md`, when present, records the independent mathematical/source review of the final report hash.

The two companion notes are cited by title. All definitions needed to follow this study are restated. The compact-sublevel theorem for the exact quartic is reused from the preceding fixed-budget note rather than reproved here.

## What the study establishes

1. Lawful native transport preserves a presented state carrier and gives a resource inequality. Two explicit examples distinguish refactoring the transported tensor from choosing a newly permitted target tensor.
2. Reverse lawful maps, a recovery test, and rank-minor certificates give checkable sufficient equality conditions. Equality of minimum values does not select an optimal implementation. A hidden-label symmetry obstructs an equivariant optimal choice in one finite example.
3. Infimizing the original resource cost over tensor fibres gives an inherited value function that composes exactly. It is generally different from the target's independently defined native cost. This is classical value-function elimination, not a computational shortcut or a novelty claim.
4. The actual quartic encoding admits exact same-budget transport on slot cores and on the nonnegative-slack zero sets. A boundary example rules out any continuously differentiable ambient lift with the prescribed core behavior.
5. The actual unweighted quartic loss and its gradients fail to commute under natural interface maps. One failure persists with stochastic observation recovery and identical exact feasible sets. A genuine announcement erasure raises the positive global minimum by at least 1/8 at budget one, with a complete proof; a separate duplicate-module example isolates residual-presentation dependence.
6. The generalized-gradient hypergraph functor is an adjoint/pullback assembly result. It is not automatically a forward interface theorem for separately built gradient flows or Euler updates.

The opening controller example explains why a mode-dependent joint specification can need more memory than its individual marginals or its report-erased version. It is an explicitly hypothetical specification, not empirical validation.

## Reproduce the checks

From this directory:

```sh
./run_exact_checks.sh
python3 check_tex_source.py
```

The final suite passes **976 exact checks** in ordinary and optimized Python. The exact-check program uses Python's standard library, rational arithmetic, and explicit exceptions rather than assertions. Optimized Python therefore does not disable the tests. The checks verify finite examples and algebraic identities; they are not a general feasibility solver, a proof of all stated theorems, or evidence that gradient descent finds global minima.

Finite exact checks include the full-support binary example, all specified transport squares, the entire quartic gradient identities, the symmetry obstruction, five algebraically evaluated zero-family samples, and regression identities for the announcement-erasure minimum gap. The all-real minimum-gap and no-smooth-lift claims are established by their analytic proofs, not by sampling.

The no-smooth-lift result, the infimum identities, and the general resource statements are justified by the proofs in the note. Numerical optimizer output is not used to certify any feasibility or global optimum.

## Source audit

The bounded primary-source audit checked the precise gradient theorem in Hanks, Fairbanks, and Klawonn, the value-function definition in Rockafellar and Wets, the classical nonnegative-rank antecedent in Cohen and Rothblum, and Stein and Samuelson's compositional convex-bifunction/value-function framework. The report gives direct bibliographic links. It does not import convex-analysis closure theorems into the nonconvex rank or quartic setting, identify this study with a proposed contextad formalism, or claim research novelty.

## Scope and execution

Run `python3 REPRODUCE.py` to run static TeX-source checks and the exact finite suites in ordinary and optimized Python. This does not verify historical archive hashes, compile TeX, or certify the general mathematical proofs.
