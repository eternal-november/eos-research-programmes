# Independent refund-formalization review

Verdict: PASS for the stated scope. No semantic defect or circular theorem hypothesis was found. This is a source-level mathematical audit plus a separate clean Lean 4.35.0 build, not a verification of the compiler or kernel implementation.

## What was checked

The reviewer read both copied dependency modules, all four new theorem modules, and sections 7–8 of `compositional.md`. The independent build uses `.independent_build`, not the author's `.build`. `independent_validate.py` rebuilds all six dependency/theorem modules plus `IndependentAudit.lean`; `independent_audit.json` records compiler version, exact source SHA-256 hashes, exit codes, and dependency printouts. No theorem source was changed by this audit.

## Ordered-group obstruction

- `OrderedAbelianGroupData` supplies genuine algebraic/order laws: associative and commutative addition, right identity, right inverses, reflexivity, transitivity, antisymmetry, and right-translation monotonicity. Commutativity gives the corresponding left laws. Inverses yield translation order reflection. These are sufficient conventional partially ordered abelian-group axioms; neither totality nor positivity is smuggled in.
- Universal agreement really quantifies over four arbitrary upward profiles. The main equivalence has only the group and arbitrary observation predicate as parameters. Factor domination is derived from the existing equivalence, not assumed as a hidden theorem conclusion.
- For a fixed observed b and arbitrary x, the proof chooses y=-x+b. Monotonicity and cancellation force a≤x, while domination supplies x≤a; antisymmetry gives a=x and hence B x. This is the intended argument.
- The constructive conclusion is precisely “any observed point forces every point to be observed.” The literal empty/all disjunction is separately proved with decidability of inhabitation or classical logic. This distinction is mathematically necessary: the new independent theorem `literal_classification_implies_em` proves, without axioms, that a literal classification for every predicate on any such group implies excluded middle for every proposition, by using the constant predicate P.
- The indiscrete Boolean preorder control has an actual XOR group, reflexive/transitive translation-invariant relation, failed antisymmetry, and nonempty proper compositional observation region. It correctly blocks extending the literal subset conclusion to arbitrary preorders.
- The concrete integer example compares upward thresholds 2 and 3, adds the upward threshold -2, and separates at budget 0. Nonpositive observations are separately proved downward closed. This is an actual compositionality counterexample, not merely failure of a sufficient condition.

## Bounded-refund theorem

- The formalized theorem is **two stages, one integer coordinate, ordinary additive cost**. It is not the full n-stage/vector/rational-weight theorem, an oracle complexity theorem, or a safe executable compensation theorem.
- The four independent lower-bound premises apply to both original and replacement profiles. They are supplied contracts, not inferred from observations. The independent Cartesian profile quantification is appropriate for this universal statement; it does not model correlations between stages.
- Input observations A and B are arbitrary predicates, not assumed lower closed or equal. The output window is inclusive `[l+r,C]`. The exact required input windows are inclusive `[l,C-r]` and `[r,C-l]`.
- Sufficiency actually holds without upward closure: every feasible witness must lie in the relevant input window by the other stage's certified lower bound. Necessity does use upward profiles, and its principal/observation-generated profiles remain admissible and lower bounded. The unchanged other stage is allowed to attain its lower bound, so there is no unproved attainability assumption about a fixed real-world profile.
- Universal necessity quantifies over all admissible profiles; it is not a claim about every individual optimum certificate or adaptive query strategy. The theorem establishes determination by fixed complete observations, not an implemented reconstruction algorithm.
- If C<l+r, all three windows are empty and the equivalence is correctly vacuous. `IndependentAudit.below_lower_sum` checks that even empty input observation regions suffice then.
- Restricting outputs to `[l+r,C]` loses nothing relative to all integer budgets ≤C: both products are impossible below l+r. `IndependentAudit.output_agreement_extends_below` proves this consequence directly from lower bounds.
- `missing_left_endpoint` and `missing_right_endpoint` independently check that omitting a single shifted upper endpoint fails whenever the output window is nonempty, even if every other integer is observed. This checks endpoint inclusion and necessity.
- The numerical example and naive-cap failure have the correct signs: lower bounds -2 and 1 and total cap 3 require windows [-2,2] and [1,5].

## Axiom and trust accounting

The clean-build printouts confirm:

- Generic group obstruction, decidability-parameterized empty/all result, and preorder controls: no axioms.
- Concrete integer group and original integer counterexamples: `propext`.
- Bounded-refund results: `propext`, `Quot.sound`.
- Literal classical classification: `propext`, `Classical.choice`, `Quot.sound`.
- Independent excluded-middle implication: no axioms. Independent bounded edge checks: `propext`, `Quot.sound`.

Thus “axiom-free” is accurate for the generic constructive group results, not for the entire package. Standard Lean logical axioms are explicitly reported; no `sorryAx` or user-declared axiom is used. Compiler success establishes well-typed proofs of the written statements, while the semantic scope qualifications above remain essential to the report.

## Limitations, not defects

No formal n-stage/vector weighted theorem, finite cardinality/query count, minimum-cost extraction algorithm, lower-bound discovery mechanism, or physical refund safety follows merely from these source files. The hand-written report contains wider results that must remain labeled as such. The classical corollary must not be described as constructive or axiom-free. Subject to those boundaries, the package supports its advertised claims.
