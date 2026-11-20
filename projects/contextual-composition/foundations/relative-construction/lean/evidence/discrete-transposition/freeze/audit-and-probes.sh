# Source from the assembled Lean root; the runner supplies the Lean invocation.
mkdir -p evidence
echo "$(date -u +%FT%T.%NZ) BEGIN ordered audit"
runlean AxiomAudit.lean > evidence/axioms.log
python3 audit.py | tee evidence/audit.log
echo "$(date -u +%FT%T.%NZ) PASS ordered audit"
(
  for f in checks/*.lean; do
    echo "$(date -u +%FT%T.%NZ) BEGIN $f"
    runlean "$f"
    echo "$(date -u +%FT%T.%NZ) PASS $f"
  done
) 2>&1 | tee evidence/probes.log
