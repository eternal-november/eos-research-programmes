#!/usr/bin/env bash
set -euo pipefail
ROOT=/workspace/shared/witnessed_B_20261024/witnessed_decompositions
R=/workspace/shared/witnessed_B_20261024/reviews/B1_Lean_Independent
source /workspace/shared/witnessed_B_20261024/toolchain_recovery/env.sh
cd "$ROOT"
sha256sum -c "$R/expected_source_hashes.txt"
mkdir -p "$R/lib/WitnessedDecompositions"
LP=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$R/lib:$LP"
: > "$R/closure_compile.log"
for m in Core Collections PathOccurrences TreeOccurrences Calculus FreeCalculus RawRefinement; do
  printf 'Compiling %s\n' "$m" >> "$R/closure_compile.log"
  lean -o "$R/lib/WitnessedDecompositions/$m.olean" "WitnessedDecompositions/$m.lean" >> "$R/closure_compile.log" 2>&1
done
lean audit/WorkstreamB1Axioms.lean > "$R/axioms.log" 2>&1
lean "$R/AllB1Axioms.lean" > "$R/all_axioms.log" 2>&1
lean -o "$R/lib/WitnessedDecompositions/Examples.olean" WitnessedDecompositions/Examples.lean > "$R/examples_compile.log" 2>&1
lean tests/B1RawRefinementAudit.lean > "$R/author_regressions.log" 2>&1
lean "$R/IndependentB1Checks.lean" > "$R/independent_checks.log" 2>&1
python research/workstream_B/B1_ChronologyChecks.py > "$R/chronology_checks.json"
sha256sum WitnessedDecompositions/{Core,Collections,PathOccurrences,TreeOccurrences,Calculus,FreeCalculus,RawRefinement}.lean audit/WorkstreamB1Axioms.lean research/workstream_B/{B1_Lean_Index.md,B1_B2_Targets.md,B1_ChronologyChecks.py} research/CompletionContract.md tests/B1RawRefinementAudit.lean > "$R/final_source_hashes.txt"
printf 'PASS: independent B1 source closure, audits, and regressions\n'
