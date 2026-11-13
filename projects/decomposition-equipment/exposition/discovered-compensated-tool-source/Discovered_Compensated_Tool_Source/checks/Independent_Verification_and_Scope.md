# Independent verification of the discovered compensated interface

## Finding

The row-space correction criterion is correct for a nonempty, stationary finite binary-linear evidence fibre. The concrete paired-job mission succeeds with partial identification under the supplied physical protocol. These are hand-proof and executable finite-check conclusions, not a new Lean formalization or evidence of physical reliability outside the model.

For `V={c:Ac=b}`, choose `c0 in V`. Then `V=c0+ker A`. The expression `c·v` is constant on V exactly when v annihilates ker A, equivalently `v in row A`. A coefficient witness supplies the value `lambda b`; different witnesses give the same value because evidence is consistent. Outside the row space, two compatible machines require opposite corrections. This is standard finite linear algebra.

The production proof additionally needs the concrete invariant `s=x+c·v`, actual useful-work tokens, one common stationary c, a known XOR correction actuator, no intervening work after sealing, and the observation/capability restrictions. None follows merely from the row-space criterion.

## Reproduction

From this directory, run:

```
python3 verify_discovered_tool.py --output algebra_check_results.json
python3 verify_tool_traces.py --output trace_check_results.json
```

Both use only Python's standard library, explicit exceptions rather than removable assertions, and no imports from the author's implementation. Normal and `python3 -O` executions produced byte-identical JSON results. Illegal-call controls execute on independent saved-state branches: each rejection consumes one real clock tick and preserves the other fields, except crossing H enters Expired. Those deliberately rejected branches are not inserted into the 64 successful deadline-tight traces.

## Algebra checks

`verify_discovered_tool.py` enumerates every linear subspace, every realizable evidence fibre, and every activity vector for dimensions 1 through 5. Concrete hidden-world evaluation is compared with linear-span membership and separately enumerated coefficient witnesses. There are 2,823 nonempty affine fibres and 83,802 fibre/activity cases. Of these, 23,561 admit a unique robust correction. Tests additionally cover dependent rows, inconsistent evidence (which must not certify vacuously), information addition/retraction, joint-versus-marginal possibilities, and a zero-weight but declared possible failure.

These finite bounds are regression evidence. The proof, not their finite coverage, supports arbitrary finite dimension.

## Concrete trace checks

`verify_tool_traces.py` independently stores the physical latch, current phase, epoch evidence, work tokens and receipts, event parity, clock, ownership, and remaining availability. Its controller does not read the private latch during production.

- 64 positive traces cover all eight hidden couplings, both desired routes, both calibration pulse orders, and both productive-work orders.
- Every positive trace pays five ticks for dummy load, two pulses, read and drain; then five for live load, two required jobs, seal and commit. Absolute completion is at T=10.
- 96 interrupted traces cover both first jobs, both targets, every hidden coupling and delays zero, one and two. With no delay, the remaining job, seal and commit fit. Delayed attempts abort safely at an explicit one-tick cost and fail the mission.
- A missing remaining-job capability does not erase the outstanding work obligation; abort leaves the already executed work and consumed token unchanged.
- Controls reject forged readout bits, withdrawn evidence, epoch-mismatched evidence, late sealing, sealed waiting, sealed Commit after withdrawal, work after seal, repeated spent work, live readout, live reset/drain, replacement loading over a pending connector, and action without ownership.
- Two actual dummy traces return the same isolated output in two machines but different outputs after A+B. The uncorrected final route is wrong in 32 of the 64 positive-test configurations.
- The q=(1,1,0) measurement leaves four worlds; C and the individual A/B effects remain unidentified.

Seal checks actual accumulated parity, not the intended plan, and reserves the two ticks needed for Seal plus Commit. The correction is an XOR toggle, never an absolute write of the desired final bit. Calibration reset is unavailable on a pending live connector. Repeating a job cannot provide free cancellation or fictitious useful-work completion.

## Scope and required qualifications

1. Safe abort needs its own tick within the guaranteed holding window. The frozen model separates mission deadline T=10 from gate retention H=11. Abort at time10 finishes safely at11; abort starting at11 is rejected, consumes its controller tick, and enters Expired without a physical safety claim. No extra tick is counted as successful mission completion.
2. Evidence/current-epoch validation is part of the trusted wrapper, not a freely asserted caller boolean. This checker retains actual acquired evidence. The epoch-change test is fault injection, not an admitted in-production reconfiguration.
3. The checker tests a fixed paired-job specialization. The general proof must retain complete history and arbitrary individual token identities; parity alone does not count work or costs.
4. Correctness of an accepted commit is partial correctness. It is not a guarantee that arbitrary waiting, refusal, unavailable work or adversarial interruption terminates successfully. A protected sealed tail is a supplied scheduler obligation; the checker rejects client waiting in Sealed. Withdrawing evidence in Sealed permits only paid abort. An unauthorized B latch mutation after seal is tested by fault injection and produces the wrong route, demonstrating the necessity of the lease.
5. Gate/owner enforcement, safe dummy mode, complete accounting of interference, route meaning, the correction actuator and stationarity are supplied. No noisy sensing, unobserved drift or unrestricted extra couplings are covered.
6. Production abstraction is exact only for the restricted guarded production alphabet. Allowing further calibration can distinguish previously compatible machines. One cannot let one fixed machine realize all responses in a version space.
7. The deterministic example requires no probability distribution. The zero-weight control only illustrates why an all-possibilities assertion cannot discard a declared outcome just because its probability is zero.

The result is a bounded application/synthesis of familiar inference and simulation mathematics, not a novel row-space theorem or generic autonomous tool-discovery theorem.

Expiry terminates the modeled attempt with stored clock H+1. Further API calls raise TerminalTrace without any modeled transition. This is not stopped physical time or certified free waiting: the model makes no safety or continuation claim after expiry. Complete and Aborted also end this checker’s single-attempt trace.
