# B2 certificate development/verification boundary

2026-10-24 UTC. These are author development notes, not acceptance evidence.

* 22:42 initial standalone example-definition check failed because the `join`
  constructor omitted explicit `(S := S)` and the nested `Shape` datatype
  requested an unsupported automatic `DecidableEq` derivation. Those were
  corrected; the initial definitions then compiled successfully.
* 22:43 the first arrow-level development check failed at attempted `rfl`
  proofs for profile grafts. The profile representation has nontrivial
  occurrence transports; replacing those claims by the accepted
  `Tree.profileGraft_corolla` theorem (and the structural/profile equivalence
  for mixed contexts) repaired the actual issue. No occurrence information was
  dropped and no extra equality was assumed.
* A broad simplification attempt at mixed grafts did not discharge the goals.
  The final proof constructs the explicit structural forest, transports it by
  `profileSubstitutionEquiv.symm`, and proves graft compatibility. This avoids
  treating dependent occurrence transports as accidental computation.
* 22:47 the complete arrow-level development check (except final composition
  definitions) passed. While the semantic-category author's module was still
  compiling, this check used its **exact Arrow definition** in a temporary file,
  not its full module. Consequently this early check is not reported as final
  integrated compilation or category-law verification. Its successful empty
  log is `B2-examples-development-arrow-check.log`.
* Final integrated checks must compile the actual `RefinementExamples.lean`
  against `SemanticRefinement.olean`, run `tests/B2RefinementExamples.lean`, and
  run `audit/WorkstreamB2ExampleAxioms.lean`. Those later logs supersede the
  development check; their outcomes belong in the final evidence inventory.

The finite checker separately passed its stated bounded domain. It is a
witness-statistic model, not a complete algorithm for the actual quotient.
