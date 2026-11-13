# Witnessed decompositions

The initial calculus retains explicit factorization witnesses, refinement data and their typed laws. Read `Results_Workstream_A.md`, the later workstream reports and `research/CompletionContract.md` with their individual scopes. The final equipment and unital-repair developments are separate packages.

Written proofs, bounded finite checks and Lean kernels are distinct evidence levels. Earlier checkpoint acceptance does not establish all later obligations.

## Formal sources

`lean-toolchain` and `lake-manifest.json` pin the compiler and dependencies. With those dependencies available, `lake build` builds the configured initial library; it is not a replay of every later workstream. Later import roots and axiom audits remain in the tree. No fresh Lean build or audit was run for this import.

`WitnessedDecompositions/` contains the formal definitions and theorems; `audit/` and `tests/` contain focused audits and checks; `research/` contains the written arguments and bounded computations. Historical workstream drivers assume archive-integrity inputs not supplied here and are not supported repository replay commands. Use the individual mathematical checks and formal modules instead.
