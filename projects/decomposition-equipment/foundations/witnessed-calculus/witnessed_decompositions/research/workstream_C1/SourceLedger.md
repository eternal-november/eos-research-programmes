# C1 source and contribution ledger

Contract v0.1, unchanged SHA-256
`47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e`.
No novelty or integrated C5/F2 result is claimed by this checkpoint.

## External baseline inspected on 2026-10-24

Gálvez-Carrillo, Kock and Tonks, *Decomposition spaces and restriction species*,
arXiv:1708.02570v1 (2017), [primary full text](https://arxiv.org/html/1708.02570).

- §2.1 supplies the retained-graph/ordered-layer construction, including empty
  layers and loss of cross-piece edges under restriction. Its graphs are more
  general and its semantics uses groupoids; C1 restricts to simple ordered
  graphs with literal equality. C1 does not claim their construction as new.
- §§5.1 and 5.5(1) identify induced graph restriction as the relevant baseline.
  C1 gives its increasing-coordinate and arrow-typed calculus proof directly.
- Their simplicial/2-Segal, incidence and CULF theorems are NOT invoked to
  discharge any F obligation here. No theorem-level F comparison is attempted.

## Internal accepted baseline

The canonical delivered source is recorded byte-for-byte in
`evidence/Baseline_Archive.json` (299 files). The separate historical local
working-copy snapshot `evidence/Baseline_Imported.json` includes 595 runtime
files and is not the delivered archive membership. All preexisting source,
contract, acceptance reports and evidence remain unchanged. Canonical baseline provenance: delivered Library source item
``, version 2, backed by parent-supplied
`/workspace/shared/witnessed_B_20261024/delivery_final/Witnessed decompositions source and contract.zip`.

- A1 supplies `Core.lean`, `Collections.lean`, `PathOccurrences.lean`,
  `TreeOccurrences.lean`, `Calculus.lean`, `FreeCalculus.lean`: typed paths,
  distinct occurrences, fibres, substitution and the genuine `Calc` interface.
- A2 supplies `FreeExtension.lean`/`FreeAdjunction.lean`: primitive assignments
  and unique strict extension. C1's model proof fills every semantic `Calc`
  field independently before using the extension.
- A3 supplies `Congruence.lean`, `QuotientCalculus.lean`,
  `PresentedCalculus.lean`: arbitrary parallel equations and universal
  quotient. C1 applies soundness to its explicit rotation/unit templates;
  it does not assert full graph-cut presentation completeness.
- B1/B2 source and accepted status are in
  `research/workstream_B/StatusLedger.json`. C1 uses occurrence-wise forests
  and `WitnessedDecompositions.RefinementComparison.evaluationFunctor` at P-level where exact
  namespace is itemized in the theorem index, not a new comparison theorem.
- Existing A4 local graph/rewrite work under `research/workstream_A/rewrite`
  contains much relevant infrastructure. Reuse is attributed and rechecked;
  full A4 scientific acceptance remains OPEN. Reused work does not acquire
  separate research credit by being linked to C1.

## Local contribution classification

This authorized milestone is a model construction/implementation and foundation
validation, not a claimed novel graph theory or new multicategory theorem.
Its useful evidence consists of the exact uniformly quantified typed calculus,
noncontiguous canonical-coordinate certificate with independently different
proper cuts of equal nonempty colours, and verified connection to the accepted
A/B representation. C1's later witness-sensitive C5/F2 integration requirements
remain unsatisfied. Counts of files, declarations and checks are coverage data,
not indicators of novelty or research significance.
