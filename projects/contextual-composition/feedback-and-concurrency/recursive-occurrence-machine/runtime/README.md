# Recursive occurrence reference runtime

This is a small, mechanically inspectable transition implementation of the proposed occurrence-process machine. It is not a static type checker, a security sandbox, or a complete implementation of the extension contract.

Run the diagnostics:

    python3 test_occurrence_machine.py

## What is implemented

- Returned values are **planar event trees with addressed holes**, not ordinary single monadic values.
- `Bind` waits for the **entire left result**, then starts one fresh continuation job per actual hole. Internal jobs have deterministic fresh identities. `phase_next()` finishes children in address order; callers can choose other enabled jobs explicitly.
- `Batch` requires an exact disjoint token partition, including a reserve child if needed. It returns a structural `Fork`, not a physical event.
- Finite raw primitive tables separate demonic alternatives from normalized rational outcomes. Zero-weight outcomes are selectable. Canonical raw identities include operation, alternative index, outcome index and displayed witness label: equal labels do not collapse distinct rows.
- Calls unfold without a fuel bound; a resolver may return `ProcedureEntry(term, value)` to separate persistent captures from dynamic input, without an extra return event; case, choice and yield are explicit steps. A prefix observation limit never creates a failure/termination result.
- Spawn uses deterministic fresh public process identities. Send transfers tokens to one message escrow; receive removes one message and combines its bundle with the receiver's current bundle. Await claims a public result at most once.
- Channels in this core are public reliable named queues, with no capability/ACL authorization check. Restricted/private channels require an explicit guard or formation adapter; token nonduplication does not imply channel access control.
- Multi-hole await returns a structural fork of the entire child tree and **one separate caller-reserve leaf**. Parent authority is not silently attached to every child result. Child and reserve positions distinguish the two branches.
- The frontier ledger separates running ownership, result escrows, message escrows and declared retirement. Historical tree annotations are provenance, not additional owners. Retyping and store changes must affect held or explicitly minted tokens only; minting requires the explicit option and a fresh identity.
- Primitive callbacks receive only their held token stores, never a global sibling-store dictionary. Shared mutable world data remain a separate input.
- `environment_step` supports declared world-only interference. Ledger-changing hostile deviations, unreliable-message policies and physical plant models are not supplied by this helper.

## Parameter and typing boundary

AST fields contain trusted total, terminating, deterministic and side-effect-free Python callbacks representing mathematical pure data functions, dependent continuation families, primitive tables and procedure bodies. They must depend only on their declared inputs. World/store changes are returned explicitly as outcomes, not performed on captured globals. The runtime does not enforce this purity assumption. This is a reference presentation, not an interpreter for arbitrary Python supplied by an adversary. A callback that closes over the machine object or other external secret state is outside the model. These callback boundaries do not provide host-language isolation or a theorem about arbitrary Python code.

A `Leaf.value` represents the **entire public post-configuration** needed by a dependent continuation, including any public response type/interface index. It need not be a scalar. `Leaf.caps` carries actual authority separately. Private store values are not automatically included in the public value. Current kinds are tracked as ledger metadata; the callback interface does not separately dispatch that kind map. Any public kind/interface index needed to select a primitive or continuation must be included in the declared public configuration. Static type/kind consistency remains a trusted formation obligation. Trusted formation of pure callbacks must ensure that authority is not copied into ordinary data; the runtime separately checks actual frontier transfers.

Malformed tables or partitions raise a Python error before the modeled transaction is committed. Such a parameter-validation error is not a semantic operation refusal. A modeled refusal is an explicit primitive outcome, and may retain reservations or prior effects. `Fault` is an explicit terminal fault record; its token bundle remains escrowed. A Batch/join waits for all children, even when one child faults; it does not cancel siblings or undo their pending effects. The resulting join has fault status.

## Exact finite bridge versus general concurrency

`legacy_oracle.py` is a separately written structural big-step evaluator for Return, primitive operation, phase Bind, structural Batch and pure Case. It does not run or reuse the small-step transition loop. It shares only the tree/AST representation and structural tree utilities. The diagnostic enumerates eight raw primitive-choice tuples and compares raw records, causal trees, exact weights, exact costs, physical chronological words and private stores with the phase-scheduled runtime.

That finite core has one relevant root computation and no external world mutation. The diagnostic is evidence for the separately proved finite bridge, not a universal proof or an assertion that all schedulers reproduce old chronology. Two bind bracketings have equal causal trees but different phase words. A shared-world test gives count 1 under interleaving and count 2 under phase serialization.

In the dynamic runtime, the **global** event ledger and scheduler/administrative trace describe the execution. `Machine.weight`, `cost` and `word` count actual primitive events once. The weight is the product of primitive probabilities conditional on the explicitly selected scheduler/alternative path; randomized scheduler or demonic-choice probabilities require a separately supplied strategy law. `Result.raw` and `Result.events` record the result's causal provenance; they are not a stand-alone probability law for a returned child under shared-state feedback. No product of terminal child marginals is used to assign a joint concurrent law. Spawned work can remain after root completion; `stop_at_root=True` is only an observation policy, not a claim of global quiescence.

## Diagnostics and limits

Tests include exact finite phase correspondence with zero weights, nullary operations, sibling private-store isolation, token partition rejection, lost updates under interference, stale revalidation retaining a pending reservation, dynamic message/result escrow, once-only result claims, multi-hole reserve framing, and an unbounded recursive prefix distinguished from blocked receive. Additional regressions reject inexact numeric coefficients and invalid transfers without allocator/transaction mutation, check administrative procedure entry, and compare a noninvertible hidden-bit world projection at every phase prefix across sixteen raw branches with exact fiber mass summation. Rejected attempts may still append an attempted-schedule diagnostic trace entry. Finite checks do not certify all executions, fair scheduling, probabilistic path construction, static formation, physical resource availability or the full contract.
