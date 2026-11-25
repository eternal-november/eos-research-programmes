# Routing late evidence to two recovery crews

[Model and proof](Two_Crew_Recovery_Report.tex) · [Lean arithmetic](SelectorArithmetic.lean)

```sh
set -o pipefail
for f in selector physical randomization seed; do
    python3 -B "$f.py" | cmp "$f.txt" - || exit 1
done
lean SelectorArithmetic.lean
```

The matched LP requires NumPy and SciPy (tested with SciPy 1.17.0). The remaining scripts use only Python 3. Lean 4.35.0 with Mathlib checks the arithmetic, not the physical interlock. The archive and cooling fixtures share an exclusive dispatch law deliberately; they are development evidence, not an independent mission transfer.
