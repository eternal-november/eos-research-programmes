# I1 mathematical proof review

31 October 2026

**Verdict: PASS for the selected finite-coefficient graph/interface class.** The reviewed proofs establish the stated conservative constructions, refinement-certificate comparisons, and conditional cut/interface transfers. This is not a claim about unrestricted amalgamation of arbitrary presentations.

## Reviewed scope and source identity

The review covers `conservative_amalgamation_theorem.md`, `interface_pushout_theorem.md`, `twisted_normal_forms.md`, `refinement_coherence.md`, `cut_transport.md`, and the optional `null_ideal_obstruction.md`. The package manifest identifies the delivered versions; `dependency_manifest.md` and `.json` identify the bundled prior results and their exact byte hashes.

The frozen author main theorem was checked at SHA-256 `5369a94bf64241c61525e356f6186c9a387442c8c6bd7a57c0de4e72edf51835`. Delivery changes reviewed separately replace draft filenames and local references with package-relative references, rename the fixed color-set notation from C to O without changing the coefficient monoid C, adjust filename-only replay metadata, and clarify the existing companion-proof and finite-test boundaries. They do not change the mathematical claims or the independent verifier logic. The null-ideal appendix preserves the reviewed obstruction and explicitly states its nonempty-color visibility condition. The delivered main file therefore need not have that author-source hash: use the final package manifest for delivered-byte verification.

The old graph scalar is terminal. Graph bound, finite interface category and finite coefficient palette vary, while profiles, arities, refinement depth and finite histories are unbounded. Full graphs, ordered occurrences, empty inputs and interface data are retained. Detecting a coefficient collapse in the graph calculus requires a nonempty color—equivalently N≥1 and nonempty K here. The N=0 and empty-K exceptions are explicitly stated.

## Proof findings

**Actual pushout and sharp interface boundary.** The interpretation argument using the monoid of diagonal-compatible unary families proves the pushout in the declared fixed-color category under the old graph calculus. The partial-map family has the exact stated quotient: precisely the block `{y_S:S⊆J}` collapses, B remains injective, and both coefficient inputs are faithful exactly when J is empty. The repaired interface embedding preserves the same abstract local and common theories. The unbounded failure is caused by actual interface identification, not an extra imposed mixed equation. The optional null-ideal appendix correctly supplies a different family in which both inputs collapse; it does not confuse that conclusion with the central partial-map family.

**Finite mixed criterion.** Unit, BAA and BBA conditions are necessary and sufficient for the specified unique AB normal forms. Termination and the complete word-overlap list are proved, not assumed. The cyclic quotient has the stated order and sharp divisibility boundary. These are comparison quotients, not bare group pushouts; standard matched-product algebra is acknowledged as baseline.

**Presented refinement coherence.** The term-level termination measure handles coefficient duplication across a branch. The syntactic overlap analysis includes old rules, coefficient rules, diagonal interactions, disjoint positions and nested variable occurrences. Well-founded normalization-path induction proves coherence modulo the explicitly generated homotopies. MOut and MIn then yield canonical full original-slot forest tuples. The independently defined refinement category and constructed inverse establish the comparison, rather than defining equality by a semantic kernel. Raw objects give an equivalence; normal objects give an isomorphism.

For a finite bare pushout, this theorem uses the chosen full multiplication-table output presentation and its specified completion. Local equations and certificates map into that completion explicitly. The operation pushout does not establish coherence of the uncompleted raw-union path category, and no such claim or two-dimensional pushout universal property is made.

**Cuts and interfaces.** Accumulated ancestor-action transport gives the exact fixed-source semidirect tree bijection. Shared parent choices and retained intermediate factors are preserved. Marked cut records are distinct from flattened refinement arrows: normalization cannot cross a marked boundary. Local-factor filtered reflection is proved; unrestricted cut fullness requires the separate factor-closure condition and fails in the displayed examples. The equivariance conditions, correlated lifting-set intersections, group-surjectivity criterion and partial-map coordinate-deletion obstruction are correct. Noninvertible old geometry still requires its own lifting theorem. No nonhomomorphic A projection is used to import the earlier product-optimality result.

## Evidence and assurance limits

The review checked the substantive derivations, the exact old-theorem signature and dependency hashes, and independently reran the principal coefficient, graph-fixture and interface-pushout regressions. The checks include mixed peaks, full-tuple countercontrols, foreign cut factors, action-aware trees and interface failures. Finite tests support the all-parameter proofs; they are not exhaustive enumeration of arbitrary proof-path quotients or a substitute for those proofs.

This was an AI-assisted review with separate automated reviewer workstreams and executable checks. Reviewers share model/tool infrastructure and may have correlated blind spots. “Independent” denotes a separate review pass and replay, not external human refereeing, an independent implementation of every theorem, or verification by a trusted proof kernel. No Lean or other formal proof-assistant certification is claimed.

The terminal PASS is confined to the named selected class, chosen presentations and certificate doctrine. It does not establish arbitrary nonterminal-scalar enrichments, unrestricted interface descent, literal equality of unquotiented directed proofs, full cut fibres, or the remaining research contract obligations.
