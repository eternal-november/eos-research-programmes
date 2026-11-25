# Source-clock uncertainty and actual receipt

[Model, evidence boundary and proof](Clock_Alignment_And_Receipt_Order.tex) · [Lean arithmetic](ReceiptOrder.lean)

```sh
set -o pipefail
python3 -B cut.py | cmp cut.txt -
python3 -B real_time.py | cmp real-time.txt -
python3 -B check_proof.py | cmp proof.txt -
lean ReceiptOrder.lean
```

`proof_pack.py` regenerates the independently checked `certificates.json`. Lean 4.35.0 with Mathlib checks the exact rational fixture, not the general graph algorithm or the input clocks. The public measured CONTEXT release motivates the provenance checks. None of its numerical observations is used in the synthetic example.
