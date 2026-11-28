# Temporal service across overlapping provisional registrations

Civilian serialized SubT broker fixture. Reuses the #912 effect-cut
check, compares against direct enumeration, and tests the predicted
failure before and after scheduling optional activation. Proof pins
capacity expiry, coherent time, eligibility, caps and deferral rights.

    bash replay.sh up | cmp - EXPECTED.txt

The Space supplement includes all pinned inputs under up. Lean 4.28.0
with Mathlib checks the finite-set and exact worst-allocation kernels.
The replay's deterministic links and post-window readiness are model
assumptions, not a field guarantee.
