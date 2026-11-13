# Independent Lean integration review — A4 / C5 / B3

**Technical verdict: PASS for the stated bounded, matched P/L integration slice.**
All new Lean declarations and the inherited A/B/C1/C2 positive regression
sources were checked from source with fresh project outputs. No theorem-source
repair was needed. This is **not** a Lean mechanization of `Comp`, its path
relations, or the uniform comparison equivalence. Scientific significance is
**NOT ACCEPTED** by this report; neither a successful kernel check nor the
standard scalar/product construction discharges that independent gate.

Reviewer: `/root/verify_integration_lean_slice`, an agent-managed non-author
reviewer. Review date: 25 October 2026. This is independent execution and
argument inspection, not independent external-human certification; correlated
model limitations remain. The full P completion proof is under the separate
review of `/root/audit_mixed_completion_proof`.

## 1. Frozen identity and scope

- Unchanged contract v0.1: `research/CompletionContract.md`, SHA256
  `47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e`.
- Frozen target: `research/workstream_integration/Integrated_Targets.md`, SHA256
  `2f8cc8b77165ef9d5fe915799e5291089067b10f0683f82d9f878ba1da1c7f7b`.
- Final author Lean manifest: `lean/SourceSnapshot.sha256`, SHA256
  `255ac3afb0c40dd0f20ebd516fae7f6e3798dafeae30abae15d566ca314f1cd1`.
- Principal implementation sources, relative to this workstream:
  - `lean/QuotientArrowCertificates.lean`:
    `c9df30048ae4755b8ae7a5ed996d537d3c222a0fe19e5aa3a89834451ca762d1`.
  - `lean/GraphForestNormalForms.lean`:
    `3a5fff106eb970e9cbcb89d45d20362c1d21e54a8f48ca04142534e5367a8980`.
  - `lean/PublicExampleBridge.lean`:
    `cd524cc6ec2b7c958d432f4f64e1f35acefc2a48313ef3202d2e4a65429f8823`.

The review inspected contract §§3.4/3.6, A4, B3, C5, and target §9. All 811
inherited files matched their preservation manifest before and after the
review. The final source snapshot and the 31 exact declaration statements and
axiom closures were independently matched. No inherited or author theorem
source was edited; reviewer checks and mutation copies are separately named.

## 2. What the checked results actually establish

### Actual A3/B2 interface

`arrow_eq_iff_entry_derives` uses the existing
`Presentation.quotient`, `Presentation.Derives`, and
`SemanticRefinement.Arrow`, not substitute definitions. For arrows with fixed
source and target, equality is equivalent to derivability between selected raw
representatives at **every original source slot**. The forward implication is
reflexivity. The reverse applies the actual quotient equality theorem at each
slot, uses `Quotient.out_eq`, and applies function/subtype extensionality. The
endpoint equation is not used to collapse different tuples.

`rawRepresentative_profile` retains the whole typed path; it is not just an
arity certificate. `entry_profiles_of_derives` consequently preserves each
entry's own path, not only the target's concatenated path. Composition
compatibility uses actual B2 composition after obtaining entrywise arrow
equality. Projection identity/composition are checked against the actual
strict-map API; these are integration regressions of accepted functor laws,
not new independent categorical-completion results.

`arrow_eq_iff_entry_codes` has a genuine and explicit **operation-level**
completeness hypothesis. It does not assume arrow faithfulness or a semantic
kernel definition of the declared equations. It also does not supply an
executable decision procedure on arbitrary quotient values: representative
selection is noncomputable and uses `Classical.choice`.

### Six-vertex full-witness forest normalizer

`forestNormal` is a dependent function on the actual `FrontierIndex t` and
normalizes each independently supplied `FrontierForest t` entry. The original
slot order is preserved; equal component colours are not used as keys.
`forestNormal_eq_iff_entry_equations` is proved by evaluating equality at each
slot and using reification injectivity in one direction, and operation
soundness in the other. It is not equality of substituted totals.

`forestNormal_eq_iff_full_local_cuts` compares full standardized local cuts,
including typed spines, partitions and values. The retained ambient graph
and each local root support are **fixed parameters** of that comparison; the
normalizer code is not a graph-independent identifier for different output
fibres. The validity assumptions are essential: standardization can discard
out-of-root vertices for invalid terms. The independent checks below expose
that failure when validity is dropped. No theorem drops that hypothesis.

`substitution_equations_at_leaves` is a structural proof with the correct right
child offset, and its nullary case requires no fictitious leaf replacement.
`graft_entry_equations` invokes the complete inherited
`Term.allLeaves_iff_entries` traversal together with `frontierDispatch_at`.
This closes the real arbitrary-forest dispatch argument rather than checking
only a single selected index. `normalized_graft_valid` adds both source
validity and the independent entry-validity conditions.

These statements range over arbitrary finite term/forest depths and arities
in the representative; they are not a bounded enumeration. The concrete
ambient set has six vertices, the interface category is the three-object
chain, and the graph module uses `ZMod 3`. The underlying inherited typed
normalizer is generic over a commutative additive monoid; the reviewer also
instantiated it in a finite noncancellative monoid.

The actual four-slot example has the mixed profile `0→1, 1→1, 1→1, 1→2` and
nonempty repeated component colours. Values 1 and 2 cancel in the total but
not in the original-slot tuple. The new theorem proves both the common
composite equation and unequal forest normal codes. The public B2 example
separately witnesses unequal actual arrows with equal substituted endpoints.

## 3. Precise P/L boundary and depth assessment

There is no all-parameter graph `Signature`/`Calc` adapter in these new Lean
files and no directly instantiated graph `arrow_eq_iff_entry_codes` theorem.
The connection between the concrete graph forest normalizer and the public
A3/B2 certificate is the explicitly documented, inherited P adapter:

1. `research/workstream_A/rewrite/LOCATED_SYNTAX_COMPARISON.md` constructs the
   two-way raw/located syntax and actual occurrence-substitution comparison.
2. `research/workstream_A/rewrite/A3_LOCAL_COMPARISON.md` §3 identifies the
   independently generated equations with actual `Presentation.Derives`;
   §§4–6 construct the independent flat-cut calculus and quotient isomorphism;
   §8 specializes and connects the checked graph representative.

The needed operation-level completeness condition is thus a proved P input,
not a new Lean axiom and not a hypothesis asserting the desired arrow theorem.
The current deliverable is an adequate **matched P/L representative integration**:
actual API-level full-tuple criteria plus a substantive concrete normalizer and
occurrence-forest proof, connected by that named P comparison. The entire
composition must be cited as **P using L components**, not as one kernel-checked
graph refinement comparison. It would be inaccurate to cite the generic code
bridge alone as an implemented graph normalizer or a formal B3 completion.

Ordinary equation-path coherence, MOut/MIn path equalities, path normalization,
fullness/faithfulness of `Comp`, all-parameter transport and factorization
statements remain P. Equality in `TypedNormalizer.E` is not equality of equation
paths. This review neither supplies nor waives those separate obligations.

The slice is more than a total-scalar or associativity-only check: it preserves
ordered local profiles, whole-fibre information, actual substitution dispatch,
nullary values and unequal tuples with common composites. Nevertheless the
new generic extensionality lemmas are elementary once A3/B2 are accepted, and
the scalar/product/pullback and ordinary coherence baselines remain standard.
No independent scientific novelty is inferred from this technical adequacy.

## 4. Independent reproduction and trusted base

Evidence directory: `review/lean_independent_20261025/`.

- Reviewer-owned `run_independent.py` copied 77 Lean source files into a new
  source tree and compiled into its previously nonexistent `fresh/` directory.
  It did not invoke the author's wrapper for the primary reproduction.
- 68 successful positive compile invocations cover 67 distinct source files,
  including the public A1–A3 roots, raw/semantic B1–B2 modules and audits,
  inherited A4 normalizer and tests, C1/C2 fragments and independent regressions,
  the new three modules and their audit.
- 682 explicit transitive axiom reports over those distinct sources cover 520
  distinct declarations. Every closure is contained in `propext`,
  `Classical.choice`, `Quot.sound`. All 31 new exact theorem statements and
  closures match the final author's theorem index.
- The positive source screen found no `sorry`, `admit`, `sorryAx`, custom
  `axiom`, `native_decide`, or `implemented_by` in compiled project code.
- All ten inherited C1/C2 negative controls were rerun and correctly rejected.
- The documented Lean 4.35.0 environment was used. The runner verified the Git
  revision of every selected package against the delivered lock file and
  constructed `LEAN_PATH` itself: only its new project output, pinned external
  package caches and the compiler standard library. No historical project
  `.olean` directory was admitted.
- The author's final portable wrapper was also independently run with explicit
  toolchain/project overrides. It passed 23 fresh modules and 31 new audits in
  `lean/runs/20261025T010227.522505Z/result.json`; its path record rejects the old
  project's `.lake/build/lib/lean`.

Trust boundary: Lean/compiler and external library caches were reused; this
was not a compiler or mathlib source rebuild. `decide`/tactic-generated theorem
proofs were checked by Lean. Inherited `#eval` examples are executable support,
not additional kernel theorems. No new theorem depends on a native oracle.

## 5. Reviewer-owned adversarial tests

`IndependentChecks.lean` has eleven checked declarations, all with explicit
transitive axiom audits. It establishes:

- The finite two-element idempotent monoid really is noncancellative.
- Two four-leaf mixed-interface expressions have equal composites in that
  monoid while one original local entry remains inequivalent.
- The generic executable normalizer is sound on both expressions.
- A nonidentity-labelled nullary is not the unlabelled nullary.
- Equal block lists and equal outer endpoints do not imply equality of the
  full intermediate-arrow profile.
- Without validity, two different terms can have equal standardized cuts;
  the precise missing hypothesis in the author theorem is therefore necessary.
- An empty external leaf is not a designated nullary.
- Changing the retained graph while preserving the relevant restricted pieces
  changes the full witness.
- The author's actual ordered-forest and actual public B2 counterexamples hold.

Five separate deliberately false files are rejected for mathematical/type
reasons: endpoint-collapse, wrong typed slot, noncancellative cancellation,
profile erasure, and nullary-value erasure. No missing import is counted as a
successful rejection.

Three source mutation copies of `GraphForestNormalForms.lean` also fail:
changing the second repeated local value to the first, deleting the nullary
value, and replacing every normalized forest entry by an identity leaf. These
are reviewer-owned copies only. They show the checked claims detect loss of
the intended information; they do not substitute for the independent C-domain
mutation suite or for proofs of the unbounded categorical target.

## 6. Disclosed reviewer harness development

The first reviewer finite-monoid declaration failed because `nsmulRec` needed
separate `Zero`/`Add` instances. The corrected reviewer probe supplies them;
its final eleven closures contain no `sorryAx`. The initial failed elaboration
log is retained and is not counted as evidence.

The primary reviewer negative-log parser initially omitted Lean's expected
`decide ... is false` diagnostic. All positive source compilations had already
passed. That parser was corrected and all ten inherited negative controls
were rerun; `result.attempt01.json` and `resume_negative.py` preserve the
history. The mutation parser likewise initially omitted `rfl failed`; its
prior result is retained and the complete adversarial suite was rerun after
correcting the diagnostic check. These were reviewer-harness false failures,
not accepted proofs or theorem-source defects.

## 7. Acceptance consequences

| Axis | Verdict |
|---|---|
| New exact Lean claims, source/axiom integrity | PASS |
| Fresh project-source reproduction and inherited formal regressions | PASS |
| Representative normalizer/full-tuple integration, with explicit P adapter | PASS within the disclosed P/L boundary |
| Direct Lean graph→public Arrow instantiation | NOT SUPPLIED; not claimed |
| Full `Comp` coherence/comparison in Lean | NOT SUPPLIED; explicitly outside this bounded L claim |
| Uniform P completion, transport and factorization proof | Separate mathematical review; not decided here |
| Scientific significance under contract §§3.4/3.6 | NOT ACCEPTED by these technical results |
| A4/C5/B3 whole obligations and integrated bundle | Not promoted by this report; B4 and other conjunctive gates remain open |

No author theorem-source correctness defect remains from this review. This
report does not amend the contract, activate another workstream, or certify
program completion.
