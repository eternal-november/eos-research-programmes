# B2 Lean source, theorem, dependency and trust index

Author-verified implementation; independent acceptance is a separate recorded
verdict. Frozen governing target and contract remain unchanged. See
`B2_GeneralComparison.md`, `B2_QuotientCertificate.md`, and `B2_Bridge_Index.md`
for assumptions, complete P arguments, and the actual raw comparison.

## Source statements and exact scope

All general modules quantify over arbitrary interfaces/quivers, arbitrary
lawful `Calc` operations in independently allowed universes, arbitrary finite
profiles, and fixed arbitrary whole c. They include nullaries. No finiteness,
decidable equality, source positivity, cancellation, object normalization, or
categorical full/faithful conclusion is assumed.

| Source | Key declarations and role |
|---|---|
| `SemanticRefinement.lean` | `Calc.composeAt_identity`, `identity_composeAt`, `composeAt_assoc` prove actual forest-tuple laws from ordinary Calc laws and typed A1 occurrence correspondence. `RefinementForest.Arrow/comp` retain explicit families and full target profiles. `SemanticRefinement.Arrow/id/comp/assoc` retain tuples and derive the category laws. `Object` is a one-field wrapper to avoid conflicting raw/free category instances. `mapArrow`, `functor`, `mapArrow_id/comp/identity/composite` define strict-map functors and tuple-level coherence. `mapArrow_injective` assumes operation injectivity, while `reflects_object_equality` separately reflects operation equality. |
| `RefinementLifting.lean` | `liftArrow_of_family` derives the missing endpoint from supplied entrywise operation lifts plus injectivity at the whole; it never assumes the desired raw endpoint. `mapArrow_surjective_of_operation_lifts` collects lifts under operation surjectivity. `mapArrow_bijective_of_operation_bijective` combines the independently proved hom injection and lifting results. |
| `RefinementFunctoriality.lean` | `functor_identity`, `functor_composite` give literal functor equalities; `functor_inverse` sends strict inverse calculus maps to strictly inverse refinement functors. |
| `RefinementComparison.lean` | Explicit inverse raw/free arrow maps and functors; `rawFunctor`, `evaluationFunctor`, their full tuple laws; automatic raw hom injection distinguished from object recovery; `unique_raw_lift_of_family`. See detailed bridge index. |
| `RefinementExamples.lean` | Nat-interface binary family, red/blue unary witnesses and loop nullaries; actual A3 all-quadruple associativity quotient; distinct raw groupings/equal quotient operations; nonthin loop and mixed-interface tuple arrows; witness invariants, nonidentity and nullary composition, fixed-target no-lift. No semantic-kernel definition of the quotient. |

The exact source hashes are in `B1_B2_SourceSnapshot.sha256`; those hashes, not
this overview, define the reproduced checkpoint. The Lean API is additionally
exercised by `tests/B2RefinementExamples.lean` and `tests/B2RawEvaluationAudit.lean`.
The latter tests prove non-surjectivity for the **actual** raw evaluation
functor in both loop and mixed-interface cases, not only for a guessed tuple.

## Project dependency separation

- Semantic core imports accepted `FreeExtension` (A2, hence A1) and the ordinary
  Mathlib functor definition. It does not import the quotient or examples.
- Lifting and literal functoriality import semantic core; the latter also uses
  ordinary `EqToHom` functor-extensionality packaging.
- Raw comparison imports RawRefinement (A1/B1), semantic core (A2), and lifting.
- Actual quotient examples import accepted A3 and the B1/B2 construction.
- No B1 proof depends on A2, A3, A4, B2 or any example. No new proof uses A4.
- B3/B4 and all C obligations remain inactive; no categorical quotient of the
  raw category is claimed.

## Axiom closure, not just textual screening

All listed audit files are run after fresh source compilation; each expected
`#print axioms` report is counted and checked against its stated whitelist.

- `audit/WorkstreamB2Axioms.lean`: generic tuple category/functor core contains
  only `propext` and `Quot.sound`.
- `audit/WorkstreamB2LiftingAxioms.lean`: supplied-family lifting uses only those
  two; optional collection of individually existing lifts additionally uses
  `Classical.choice` (explicit classical choice in its proof).
- `audit/WorkstreamB2FunctorialityAxioms.lean`: identity equality uses only the
  core axioms; literal composite/inverse packaging additionally uses standard
  `Classical.choice` via the imported functor equality/composition machinery.
- `audit/WorkstreamB2BridgeAxioms.lean`: actual forest/tuple maps, evaluation
  functor/laws, automatic hom injection and unique supplied raw lift use only
  core axioms; the two inverse-functor equality packaging theorems additionally
  use standard choice, separately disclosed in the bridge index.
- `audit/WorkstreamB2ExampleAxioms.lean` and actual-quotient tests additionally
  use accepted A3's `Classical.choice` for representative selection.

No custom axiom, admission, `sorryAx`, or unchecked computation oracle is
allowed. The source screen removes comments/strings before checking forbidden
commands; kernel dependency reports independently inspect actual proof terms.

## Verification chronology and failures

The first semantic elaboration failed at dependent identity/profile transports,
subtype elaboration, and implicit functor syntax. The repaired source explicitly
transports the identity profile family and proves full `composeAt_assoc`; the
second elaboration passed. No tuple or profile information was dropped.

The example worker first checked definitions and arrow proofs with an exact
local copy of the Arrow definition while semantic core was still compiling.
That development check is NOT final category evidence. The later actual-source
`B2-examples-integrated-build.log`, `B2-examples-regression.log`, and
`B2-examples-axioms.log` supersede it and pass against the real module.

An interaction interruption ended the earlier workers after those completed
checks. Disk/process inspection found no running Lean task; the missing bridge
and explicit lifting files were completed in new work without repeating or
claiming the unfinished attempt. The supplied-lift module compiled on its first
attempt. Literal functoriality needed two elaboration repairs (explicit functor
arguments and avoiding a tactic after a solved identity goal); its third run
passed. Bridge repair history is preserved in its separate index.

Finite checks remain C evidence, not quotient completeness or unrestricted
proofs. `examples/check_semantic_refinements.py` relative to this directory
checks the declared 81/3/750/375/183 cases; its witness-statistic target may
identify further operations and is never used as the definition of A3 equality.
The aggregate `verify_workstream_B.sh` rebuilds the complete original export,
then explicitly recompiles accepted dependencies and all new modules into a
fresh Lean output directory, runs audits/negative tests, and reruns finite
certificates. A normal baseline `lake build` alone does not compile these new
modules because the original accepted aggregator is intentionally unchanged.
