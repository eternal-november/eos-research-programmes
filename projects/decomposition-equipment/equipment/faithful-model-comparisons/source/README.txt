E3 Substantive models and faithful comparisons

This source package contains the local original-E3 P proof, bounded C evidence,
checked typed core, minimal retained premises, clean acceptance and report.
It does not claim full Lean formalization, E4 ordinary completion or global
workstream acceptance. Read report.txt first, then theorem.md and the exact
source_obligation_map.md. The historical contract remains byte-preserved.

Evidence boundaries

P    theorem.md proves the full parameterized graph-groupoid and graph-span
     equipment assertions and comparisons, crediting the inherited SPAN and
     accepted E1/E2 results. The finite-groupoid restriction is g^-1 h f.

C    checks/ implements actual finite cells and factorization tests, all three
     Python optimization modes, semantic mutations and source/output guards.
     Its final receipt does not prove arbitrary-parameter P assertions.

L    formal/ contains the exact original source, inherited E1 modules, two new
     E3 modules and source-only runner. Read formal/P_CORE_ADAPTER.md and
     formal/README_FORMAL.md for the exact typed-to-classical bridge and limits.
     The full graph-span comparison remains P, not a new Lean theorem.

Verification

From checks/ run:

    python3 -B run_e3_checks.py --output /tmp/faithful-model-comparisons-checks.json

These are bounded finite checks, not a full proof audit. Formal source packages retain their own pins; no fresh Lean replay is claimed. See the project VERIFICATION.md for evidence boundaries.
