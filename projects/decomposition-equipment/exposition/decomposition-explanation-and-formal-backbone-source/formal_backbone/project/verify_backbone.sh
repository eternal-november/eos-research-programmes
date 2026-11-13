#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p fresh_logs
lean --version | tee fresh_logs/toolchain.log
lean --version | grep -q 'version 4.35.0'
# This default build includes BOTH the recovered core and every new module.
lake build > fresh_logs/default_build.log 2>&1
for audit in FreshCoreAxiomAudit JointQuotientDecoderAudit JointArrayDecoderBridgeAudit CompressionAudit NewBackboneAudit; do
  test -f "$audit.lean"
  lake env lean "$audit.lean" > "fresh_logs/$audit.log" 2>&1
done
if grep -E 'sorryAx|error:' fresh_logs/FreshCoreAxiomAudit.log fresh_logs/NewBackboneAudit.log; then
  echo 'Unexpected axiom/error in audited proof closure' >&2; exit 1
fi
printf 'PASS: recovered core and every required new proof module\n'
