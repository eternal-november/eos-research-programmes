# Retry capabilities and deduplication

A finite, serialized worked integration of catalogue items 38–39 with the existing contextual-composition interface and simulation machinery.

Run `python3 check.py`. The script uses only the standard library and exact arithmetic.

The note proves at-most-once safety, a sharp `2^m` deterministic decision-state lower bound for independently replayable keys, and an interface-relative safe-forgetting criterion. It distinguishes acknowledgement from physical execution and makes the atomic effect/logging assumption explicit. These are elementary protocol/automata arguments, not a new general categorical theorem or novel RPC protocol. No Lean replay or network validation is claimed.

Retirement is pathwise under identical loss witnesses. Equal loss kernels on related states suffice for stochastic/contextual preservation (they are not necessary for equal observable laws); arbitrary private-state-dependent losses can distinguish forgetting even when retired keys are never called. The script includes both the equal-kernel case and a counterexample.
