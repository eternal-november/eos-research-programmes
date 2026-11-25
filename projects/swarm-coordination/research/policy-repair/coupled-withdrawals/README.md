# Coupled withdrawals across recovery queues

[Proof and scope](Coupled_Withdrawal_Closure.tex). Exact least withdrawal under fixed lists, independently compared to a direct Horn encoding and brute force. Composition separates common claims from local authority and costs. No whole-system or independent mission evaluation.

```sh
PYTHONHASHSEED=0 python3 -B replay.py | cmp - results.json
```

Lean 4.35.0 with Mathlib checks the three abstract laws in `CoupledQueues.lean`.
