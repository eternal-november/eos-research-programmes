# Recursive occurrence processes and the exact finite bridge

Read the [self-contained TeX manuscript](Recursive_Occurrence_Processes_and_Finite_Bridge.tex) and [reference runtime specification](runtime/README.md).

This moves from the earlier [native constructions](../native-first-results/README.md) and [information/progress criteria](../information-and-progress/README.md) to an actual recursive occurrence machine.

## What is supplied

- Addressed multi-hole returns, whole-left-phase Bind, separated structural Batch, explicit recursive unfolding and scheduler choices.
- Dynamic spawn, public reliable message queues, token/message/result escrow, and once-only multi-hole await with a separate caller reserve.
- Mutable shared-world effects distinct from the unique frontier authority ledger; stale revalidation can refuse while retaining pending effects.
- An independent structural old evaluator, plus a ranked-template adapter separating persistent captures from dynamic input.
- A written exact phase-scheduler bridge, including zero-weight raw choices, chronology, cost and final live private-store observations.
- A category of strict primitive-model maps and uniform directed prefix/path comparisons across the supplied recursive/concurrent constructors.

The tests include actual lost updates under interleaving, pending-reservation preservation, private-store isolation, duplicate-label zero branches, unbounded recursive prefixes, and a noninvertible world abstraction checked at every prefix.

## Exact boundaries

The finite bridge uses the pinned old primitive tables, the phase scheduler, deterministic allocation and no undeclared external mutation. It does not identify arbitrary concurrency schedules with the old evaluator or turn causal Bind associativity into chronological equality.

The Python implementation uses trusted pure callbacks for data families, procedures and primitive tables. It is not a static typechecker or a host-language security boundary. The ledger is not proof of physical authority or availability. Public channel names do not implement channel ACLs. The environmental helper changes the shared world only; ledger-changing hostile deviations need an additional checked signature.

A strict model map must preserve actual joint primitive/world/store/transaction and history-observer squares. It is not an arbitrary coupling span or an automatic extension of every old quotient. Local raw surjectivity is separate from probability pushforward.

This is substantial scoped RC1/RC7 groundwork, not completion of those obligations or the entire feedback/concurrency contract. Written proofs and independent finite diagnostics are not Lean certification. No historical novelty or TeX compilation is claimed.

## Reproduce the checks

From this directory:

    python3 runtime/test_occurrence_machine.py
    python3 runtime/test_ranked_adapter.py
    python3 runtime/check_runtime_interfaces.py
    sha256sum -c MANIFEST.sha256

Tests do not use the small-step runtime as their structural big-step oracle. The runtime and adapter check executed paths and table transactions; trusted formation of all unexecuted callbacks/branches remains an assumption.
