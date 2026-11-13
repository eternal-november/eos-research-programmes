# Witnessed decompositions — B1/B2 checkpoint

Start with `Results_Workstream_B.txt` and the new
`research/workstream_B/StatusLedger.json`. The original `README.md`, original
A reports, manifests and acceptance ledger are preserved byte-for-byte as the
imported A checkpoint; they are historical scope-specific documents, not the
current B verification instructions.

The authoritative `research/CompletionContract.md` is unchanged. A1–A3 retain
their original accepted status. A4 remains LOCAL_VERIFIED / OPEN. This checkpoint
adds only B1/B2; it does not activate B3/B4 or any C obligation. Standard
infrastructure is identified as such, not advertised as novel research.

## Formal verification

The pinned Lean sources include `WorkstreamB.lean` and named B axiom audits. A plain `lake build` targets the initial A library, not the entire B development. The old combined archive driver requires absent archive-integrity inputs and is not a supported replay command here. No fresh Lean replay is claimed.

## Evidence and packaging

- `WitnessedDecompositions/RawRefinement.lean`: actual raw forests, category,
  thinness/antisymmetry and typed occurrence coherence.
- `SemanticRefinement.lean`, `RefinementLifting.lean`,
  `RefinementFunctoriality.lean`, `RefinementComparison.lean`: arbitrary target
  tuples/category/functors, explicit lifting hypotheses and raw comparison.
- `RefinementExamples.lean`: actual A3 typed associative quotient with retained
  witnesses, nonthin semantic arrows and genuine mixed-interface contexts.
- `research/workstream_B/`: frozen pre-attempt target, complete mathematical
  dossiers, prior-theory comparison, exact theorem/dependency indices, retained
  failed-attempt logs, independent review/checker sources and verification receipts.
- `audit/WorkstreamB*.lean`, `tests/B*.lean`: kernel regressions and axiom closures.
- `B1_B2_SourceSnapshot.sha256`: exact new mathematical/source verification scope.
- `B_EXPORT_FILES.sha256` and `B_EXPORT_MANIFEST.json`: complete deliverable bytes.

L (Lean kernel), P (complete written mathematical proof), and C (bounded
computation) are separately labelled. The archive includes source and selected
public logs, not compiler/dependency binaries, generated oleans, captured process
environments, or private agent coordination. Reviewer reproduction scripts with
historical absolute paths are retained as historical evidence; the root B driver
is the portable recommended command. Independent review is non-author automated
review, not external human certification.

The restored official compiler archive was SHA256-verified and all dependency
Git pins checked. Official mathlib compiled cache use is disclosed; not every
external dependency was rebuilt from source. All project theorem sources were
freshly compiled. Toolchain receipts are under `research/workstream_B/evidence/toolchain/`.
