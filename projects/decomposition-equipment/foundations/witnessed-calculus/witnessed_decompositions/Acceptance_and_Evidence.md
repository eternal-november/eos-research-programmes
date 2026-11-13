# Acceptance, evidence, and reproducibility

Checkpoint date: 24 October 2026 UTC. This is a reader-facing account of the completed decisions and their evidence, not a replacement for the governing contract. The exact contract SHA256 is `47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e`.

## Current decisions

The acceptance records in `research/AcceptanceLedger.json` were made after mathematical/scope review and final reproduction of the frozen sources:

- **A1 ACCEPTED**, 18:28:08 UTC. Arbitrary-signature typed operation fibres, ordered occurrence transport, full substitution laws, independent tree-representation comparison, and the calculus/morphism specification.
- **A2 ACCEPTED**, 18:37:52 UTC. Arbitrary-target extension and preservation, uniqueness among all strict morphisms, inverse hom correspondence, both-variable naturality and the free/forgetful adjunction. The required second target is the uniformly proved arbitrary-relation calculus, with bounded independent computational controls.
- **A3 ACCEPTED**, 18:43:42 UTC. Arbitrary parallel equations, the least substitution congruence, actual quotient calculus, arbitrary-target universal factorization, and the exact relation between derivability, quotient equality, and all-model equality.
- **A4 LOCAL_VERIFIED, with full obligation status OPEN.** The local mathematical verification was recorded at 18:56:30 UTC, with final documentary review at 18:58:37 UTC. `rewrite/A3_LOCAL_COMPARISON.md` proves the exact connection to the accepted A3 signature, independently generated equations and actual quotient. Local normalization is not the contract's integrated refinement-arrow comparison or downstream use.

Acceptance is confined to these obligations and evidence boundaries. This is not acceptance of all Workstream A, the entire research program, or any blanket mathematical novelty claim. “Independent” in the development evidence means a separate automated mathematical review/reproduction, not external human certification.

The unmodified contract describes original OPEN obligations; the derived ledger overlays the later A1–A3 decisions without rewriting their original clauses. Consequently, an original clause's embedded OPEN wording is not an inconsistency with a later ACCEPTED status field. A4's cross-workstream gate remains real: §3.6 groups A4, B3–B4 and C5; C1 also requires actual downstream use. Object normal forms alone cannot supply the missing refinement categories, arrow comparison, coherence, transport, recoverability, or use theorems.

## Evidence classes

- **L:** declarations checked by the Lean kernel, with named transitive axiom reports.
- **P:** complete written mathematical proofs, which require mathematical reading rather than execution alone.
- **C:** bounded executable checks and negative controls. These strengthen diagnosis and test coverage, but do not prove unrestricted quantified claims.

No finite enumeration is relabeled L or P. `#eval` output is an executable regression result. `decide` used in checked theorem proofs is kernel computation; the included sources do not use `native_decide` as an unchecked theorem oracle.

## A1 coverage

The public source proves genuine operation substitution at independently specified path profiles. Input occurrences are ordered positions, not component names, so repeated equal colors remain independent. Canonical slot-expansion/component/coherence theorems are explicit. Both unit laws and associativity are proved in the prescribed fibres, not replaced by agreement of flattened frontiers. Source associativity is derived structurally, not supplied as an assumed `Calc` field.

The P dossiers `A1_RepresentationProof.md` and `A1_CalculusComparison.md` cover independent finite planar edge/vertex incidence data, reconstruction in both directions, occurrence order/grafting, arbitrary-fibre versus total-space representations, and the exact admissible-profile restriction of ordinary colored nonsymmetric multicategories. They do not define the supposedly independent representation as an alias of the Lean datatype.

Regression tests include mixed interfaces, branching followed by nullary deletion, repeated colors receiving different replacements, explicit generator-order checks, and wrong endpoints/order/nonloop-nullary rejection. The generic positive-signature theorem separately identifies the nonempty subcalculus. No finite-base, decidable-equality, inhabitedness, or one-object restriction is inserted into the core quantifiers.

Main sources: `Collections.lean`, `PathOccurrences.lean`, `Positive.lean`, `TreeOccurrences.lean`, `Calculus.lean`, and `FreeCalculus.lean`. Audit: `audit/WorkstreamAReview.lean` and `audit/WorkstreamAAxioms.lean`.

## A2 coverage

`FreeExtension.lean` interprets every finite source tree in every target calculus, preserving the exact occurrence-wise forest substitution. Target identities, rather than arbitrary component atoms, interpret leaves. The uniqueness proof derives the recursion from corolla decomposition and strict substitution preservation; it does not assume the desired recursion in its competitor class.

`FreeAdjunction.lean` supplies naturality, map/functor laws, unit/counit triangles, raw/profiled signature comparisons and categorical packaging. The hom correspondence explicitly permits independent target operation universes. `tests/A2CoreAudit.lean` demonstrates distinct strict extensions from distinct parallel primitive assignments, and rejects invalid output/profile assignments.

The second target in `relational/RelationalTargetProof.md` consists of arbitrary multi-input relations on arbitrary component-indexed carriers, with equality identities and existential occurrence substitution. Its complete laws and transport comparison are P, not a fully packaged Lean `Calc` instance. The optional Lean witness-assembly fragment and coherence-dependency audit are explicitly separate.

The included finite oracle exhaustively checks 26,879,044 associativity equalities, 552 unit equalities and 102,724 independent composition-table comparisons in its stated Boolean finite-arity domain. It additionally checks 18 recursive/global-edge comparisons, 9 syntax-identity cases, 9 assignment squares, 7 typing rejections, and 3 semantic mutations. Repeated-slot identification, repeated-slot swapping and an incorrect universal identity are detected. The complete domain, actual multivalued tables and separating context are retained in `FiniteModel.md` and `FiniteChecks.json`.

## A3 coverage

`Congruence.lean` starts with independently declared parallel equations and inductively generates equivalence and simultaneous-substitution closure. It proves parallelism and leastness without referring to any model or normalizer. `QuotientCalculus.lean` proves exact-profile representative choice, representative-independent substitution, quotient unit/associativity laws, a strict projection, arbitrary-target descent and all-map uniqueness. Choice of representatives is disclosed and is not a computable normal-form assertion.

`PresentedCalculus.lean` connects the free and quotient constructions to the presented hom correspondence and target naturality. The all-models quantifier contains the actual constructed quotient model, which gives completeness; soundness holds for arbitrary target universes. The quotient is not simply declared equivalent to one preferred model.

`PresentationExamples.lean` and `WeightInvariant.lean` treat a nontrivial associativity declaration across four interfaces and prove separation of an undeclared red/blue equation. The independent XOR relation interpretation supplies a second separation explanation and an executable truth-table certificate. `tests/A3CoreAudit.lean` proves that a deliberately lossy model can identify red and blue without derivability, and that adding the missing declaration changes derivability. Wrong-profile equations and nullary/repeated-occurrence behavior are tested.

## A4 local scope and limits

The P theorem in `rewrite/THEOREM.md` is parameterized by the finite graph bound, finite interface category and arbitrary finite commutative witness monoid. The bound constrains the retained graph, not term depth. It retains full graphs, ordered partition/inclusions, every interface arrow and the total decoration. Seven interacting rule families cover rotation, both unit eliminations, identity decoration, aggregation, and movement from either cut argument. The proof supplies decidable matching, a strict lexicographic reduction measure, irreducible classification, full semantic completeness and an exhaustive 18-family overlap analysis.

The substantial Lean instance covers arbitrary finite well-typed terms on a three-object chain, Z/3 decorations and support subsets of a six-vertex ambient graph. The file name `RewriteFragmentCandidate.lean` is retained to preserve exact source bytes; it is the delivered local representative, not an omitted exploratory sketch. `TypedNormalizerAlgebra.lean` supplies independently generated equations and a sound/complete executable normalizer. `GraphCoordinates.lean` and `RewriteFragmentCandidate.lean` supply exact cut coordinates, validity and witness preservation, repeated-component distinctions, and the general finite-forest traversal/offset correspondence.

The unrestricted all-rewrite-sequence termination argument remains P. The Lean representative proves its executable normalizer, generated-equation soundness/completeness, output irreducibility, and graph-valid substitution. It does not separately mechanize the whole parameterized lexicographic termination proof. `LOCATED_SYNTAX_COMPARISON.md` is the explicit P-level two-sided raw/located comparison. The final `A3_LOCAL_COMPARISON.md` then gives the exact finite equation templates in `Presentation.Equations`, proves agreement of the rewrite and actual A3 generated congruences in both directions, constructs the independent flat-witness `Calc`, and proves inverse strict maps between it and the actual `Presentation.quotient`. It retains zero/one-frontier cases, all occurrence substitutions, full witness data and the correct model-universe boundary. This is P linkage reviewed as LOCAL_VERIFIED, not a claimed general Lean adapter.

Finite graph-labelled controls cover 52,147 critical-shape instantiations and 121,626 one-step reducts, with an additional six-vertex repeated-nonempty certificate. A separately implemented structural oracle checks 25,779 terms of at most seven constructor vertices, 111,708 contextual steps and 9,841 increasing-restriction compositions. Its structural domain does not cover all graph labels/interfaces. All domains and limitations are in the supplied JSON. Missing movement causes two distinct normal forms, reverse rotation creates a cycle, and a concrete noncommutative transformation monoid exposes the necessary commutativity hypothesis.

`LIMITS_AND_SOURCES.md` supplies the exact unary-word reduction from arbitrary finite monoid presentations and primary-source provenance for the unrestricted undecidability limit. That limit does not contradict the positive selected fragment.

## Trust and audit policy

A1/A2 required core closures are restricted to standard `propext` and `Quot.sound`. Optional bundled adjunction packaging additionally uses standard `Classical.choice`. A3 closure/core audits retain the narrower set; the quotient construction and corresponding adversarial test disclose `Classical.choice`. Some A4 graph/irreducibility proofs also use the standard three-axiom set. The export driver retains these separate limits rather than broadening all audits indiscriminately.

For every supplied audit command, the driver checks that the number of emitted axiom reports equals the number requested, then checks every reported dependency. It also screens source commands for placeholders, custom axioms and unchecked computation oracles. This is a check of the named audited closures and the supplied source, not a claim to have reimplemented or independently proved the Lean kernel.

The official Lean 4.35.0 release and matching pinned mathlib cache were used historically. The export driver builds the public library and then recompiles all project theorem modules in a new output directory, followed by the tests and fresh A4 modules. It does not claim to rebuild every mathlib dependency or compiler binary from source.

## Failures and chronology, without counting failed runs as proof

- A1's nested occurrence audit initially timed out at 200,000 and 2,000,000 heartbeats, and a direct reflexivity attempt failed. The repaired proof established the first-layer constructor/function extensionality before computing the second layer; the full assertion remained intact.
- A2's strict-map test had an initial elaboration failure, repaired before its successful accepted reproduction.
- A3's first fresh-directory check failed because of import layout. The repaired fresh build and final accepted reproduction are separate evidence.
- The A4 finite-forest dispatch initially lacked a proof connecting frontier positions to recursive substitution offsets. The general `Term.allLeaves_iff_entries` correspondence, `frontierDispatch_valid`, and `valid_frontierForest_graft` repaired that gap. A bounded example was not used to bypass it.
- A4 had class-level conditional scope review before its P draft, but exact-schema review of all seven rules occurred after the first draft, at 17:59 UTC. That chronology is disclosed; it is not retroactively represented as a completed exact-schema pre-proof gate. No contract weakening resulted.

Raw development failure/coordination records and private review prose are not distributed. This account preserves their materially relevant failures and evidence limits. Selected accepted logs are retained byte-for-byte; an unsuccessful execution is not included in the accepted evidence set.

## Exact evidence and packaging provenance

Historical accepted reproductions:

- A1: `logs/workstream-A-verification-20261024T182717Z.log`.
- A2: `logs/workstream-A2-20261024T183621Z-verification.log`.
- A3: `logs/workstream-A3-20261024T184253Z-verification.log`.

Their hashes are verified against the unchanged acceptance ledger. Related accepted axiom and finite outputs are also included. The A4 representative reproduction is `logs/root-A4-representative-20261024T1842.log`. The full local mathematical reproduction is `logs/workstream-A4-local-20261024T184925Z/verification.log`, with its exact finite reports and Lean axiom outputs. The final local proof hash in `research/AcceptanceLedger.json` is `e7c3d7e547f60e77ef818232692887bcb0d1180a3a7cb39d9e5225c1ffb8ce24`; it is not an A4 scientific-acceptance record.

The original A1–A3 snapshot files and final `A4_LocalSnapshot.sha256` are preserved under `historical/snapshots/`. The latter has SHA256 `7cf483167326b71b9ef3ec7b90beac9f206276f367803b97799d9d00153874a0`. Some entries describe intentionally omitted freeze/coordination/review artifacts. `EXPORT_MANIFEST.json` identifies every retained entry and every omitted snapshot entry. The original scripts are retained under `historical/scripts/` for provenance, not used as the export driver. The independent executable A2/A3 tests and structural finite checker were moved to `tests/` with their bytes unchanged. No imported Lean namespace was renamed.

Older proof-dossier path references resolve as follows:

- `FreeAdjunctionCandidate.lean` / `FreeAdjunctionStable.lean`: the exact same source is now `WitnessedDecompositions/FreeAdjunction.lean`.
- The generic quotient candidate: the integrated implementation is `WitnessedDecompositions/QuotientCalculus.lean`.
- `research/workstream_A/review/A2CoreAudit.lean` and `A3CoreAudit.lean`: unchanged copies are under `tests/`.
- Old per-stage verification commands, `env.sh`, draft freeze/review reports, and candidate-only print utilities: replaced for reproduction by `verify_export.sh`, its explicit checks, and this evidence account. Their absence is not a missing theorem dependency.

`EXPORT_COPIES.json` records every byte-identical copy's original relative path, SHA256 and length. New packaging documents/scripts are separately classified in `EXPORT_MANIFEST.json`. The contract, actual theorem sources, retained mathematical proofs, and historical source-hash snapshots were not modified to make this export pass.

## Fresh export verification and final documentary refresh

The complete `verify_export.sh` run started at 18:52:05 UTC and passed all fresh public theorem builds, negative/adversarial tests, named axiom closures, representative A4 builds/tests and four finite certificate families. The unchanged output summary and complete execution log are `evidence/export-verification-20261024T185205Z.json` and `.log`. The mathematical P proofs are not certified by that script; their reviewed scope is stated above.

After this executable run, the final report/acceptance/obligation/validation metadata and the metadata-building utility were refreshed; `A3_LOCAL_COMPARISON.md` and the final A4 snapshot/logs were added. `LOCATED_SYNTAX_COMPARISON.md` now explicitly explains the already-checked traversal repair and exact A3 linkage. `LIMITS_AND_SOURCES.md` updates its local-verification versus remaining-gate section. The exported README and this synthesis were updated to match. These are documentary/local-proof and packaging changes, not changes to any Lean theorem or finite-check implementation.

All 35 Lean source/test files, all four finite-check scripts, `verify_export.sh`, and `scripts/verify_export.py` are byte-identical to the successful full export run. A1–A3 accepted mathematical proof bytes and source snapshots remain unchanged. The final manifest-only check was rerun, all retained final A4 snapshot entries were compared explicitly, and the linkage proof hash was checked against its final ledger record. No claim is made that rerunning a checksum constitutes fresh mathematical review.
