# Exact finite verification of crossing certificate transport

31 October 2026. Independent executable corroboration. **PASS: 112,676 exact assertions.** Standard-library Python only; rational probabilities use `fractions.Fraction`. No random sampling, network access, external packages, uploads, or global response table supplied to a local owner.

Run:

```sh
python verify_crossing_certificate.py
```

The program regenerates `verification_crossing_certificate.json`; the same captured console output is in `verification_crossing_certificate.stdout.txt`. SHA-256 of this verifier version: `bd3b5052c36927faf64b95acebcd8df12a594c2b8545efcc4d0db197226c732d`.

## What is actually executed

`run_local` branches at individual local fair-source instructions. It starts with one initial event and executes one or two source events per tile. Column owner 2 computes from the delivered intermediate parity and its own innovation. The row parity owner computes only after the two-bit delivery. Tile-local environments are discarded; the outgoing parity is the only inter-tile state. Immutable `rep:r0` / `rep:zi` names are minted once. Trace and complete path collections are write-only verifier instrumentation, not information delivered to owners. Analytic source enumeration is a separate oracle used after execution, never the representative implementation. An AST dependency check additionally rejects calls from the interpreter to the analytic chain/subspace enumerators.

For n=1 through 8, every branch verifies source identity, positive weight, exact normalization, fine-record equality, grouping/ungrouping coherence via stable indexed merge (with a negative control rejecting naive row-owner concatenation), output occurrence identity, chart message counts and uniform diagonal mission law. Odd final cells are included. The two ownership partitions have four singleton intersections and are nonlaminar; this is not asserted to be an original ordered-C5 refinement. Common semantic records retain source and XOR-wire identities; chart-specific physical message records remain in side ledgers. Their removal from the semantic projection is **not** a resource-equivalence assertion.

The artifact's separate canonical **7m+3 witness-tick schedule** is also checked directly by `scheduled_tile`: eight local boundary/source assignments execute seven named draw, delivery, XOR and seam transitions; delivered-view and source-phase guards are checked, and the shared intermediate parity slot retains one writer and one reader. Both ownership policies have exactly the same elementary schedule and resource record. This is distinct from the physical-controller fixture below. Tiny basis-mask checks enumerate every ordered list of up to three 3-bit rows, reject incomplete spans, and check exact endpoint support; symbolic XOR cancellation checks the telescoping residual. The formerly proposed 8192(n+K+1) envelope is not assumed. The separate executable normalized compiler and proved 445n+597 instruction ledger are documented in `verification_crossing_compiler.md`; this probability verifier is not used to measure compiler latency.

## Tests beyond the maximal representative

| Updates n | All subspaces of free-coordinate space | Compatible supports | Proper compatible supports |
|---|---:|---:|---:|
| 2 | 16 | 3 | 2 |
| 3 | 67 | 13 | 12 |
| 4 | 374 | 83 | 82 |

All compatible supports pass equal-fiber Q pushforward and all four coordinate-test expectation checks. For n=2 through 7, explicit physically realizable z1=z2 supports retain every original triple/endpoint law and Q law, while the enlarged z1+z2 query distinguishes them from independent innovations. Thus testing is not confined to uniform V, nor does it imply full early-transcript equality. The general theorem's linear-fiber and test-pullback arguments remain proof obligations; finite checks are corroboration.

## Actual physical controller modules

`controller` is a separate deterministic interpreter, not a stochastic representative. It takes **actual** early captures and executes the column or row XOR modules. For n=2,4,6,8, all 2^(n+1) early streams, including the correlated subclass, give identical intermediate parity values and the same final p. For either possible physical d, both controllers have identical p+d. No independence assumption is used in this pointwise check.

This includes a concrete, explicitly supplied hardware fixture: all early captures at time zero, available after one tick, charged n+1-bit sensor storage; one tick per XOR and per message; a row two-bit message requires two-bit word capacity. Each tile takes three ticks, each inter-tile seam one tick, and final gate setup one tick. Therefore the required selected-slot deadline is 2n+1 ticks. Column delivery is n−1 bits and row delivery is 3n/2−1 bits, including inter-tile seams. These are illustrative certified-cost inputs, **not** measured latencies or a universal schedule. A one-tick shorter deadline or insufficient row capacity refuses this implementation.

Removing the row's only timely u delivery invalidates this restricted implementation. Exhaustion of all 16 deterministic response functions of (a,v) shows exactly 1/2 success for recovering a+u under an independent fair hidden u; independent randomized mixtures cannot do better. This is an architecture/view restriction, not impossibility for every physical policy. Restoring the bit repairs the local computation only if capacity and deadline checks pass. An already available direct source/readout or alternative sufficient message would change the negative premise.

## Evidence, guard and repair tests

- A versioned certificate fixture preserves physical block/clock/gate/pulse/drain IDs, physical uncertainty K, evidence version and the single confidence allowance under certificate-only chart transport.
- Stationarity, isolation, H+D freshness, compute/gate latency and budget violations each invalidate acceptance. Replayed charts add their own capability and resource checks; certificate-only regrouping does not invent a physical messaging requirement.
- For every n=2 through 7 and every deleted triple, 27 defects retain all undeleted triple and endpoint laws but change the old mission risk to exactly 1/2. The verifier explicitly instantiates these as stationary finite-memory lag/mask filters: each captured register addresses the same original innovation-time vector, and the delayed endpoint contains the propagated extra fair defect. The selected defect load delay is D=2n+2, leaving a spare tick after the physical-controller fixture readiness deadline; intermediate register delays are τ_i=i. H+D start spacing gives disjoint innovation windows.
- Exact four-sample reacquisition illustrates rather than assumes behavior: the good plane is recovered with probability 105/128; a truly defective full triple space falsely presents exactly that plane with probability 105/2048. It is therefore wrong to say that reacquisition necessarily restores the old relation in a changed source.
- The **budgeted** evidence-repair fixture separately uses seven samples, not four: dimension ceiling 3 plus four confidence bits gives allowance 1/16. It charges seven H+D reservations and checking (93 fixture ticks), increments the evidence version, and adds this fresh allowance to the original 1/32. Insufficient remaining budget refuses this method, not every mission. Merely changing charts does not add another delta.

## Optional-delay distinction

The finite optional-delay fixture retains a selected diagonal endpoint and an additional diagonal candidate endpoint. Its full evidence support has 8 records; a chain-only lifted relaxation has 16 and changes the unselected candidate law while leaving selected Q unchanged. The crossing representative does not output that omitted coordinate. In this simple fixture the projection to selected captures happens to equal the chain support; the test makes **no general claim** that all-evidence projection equals the relaxed captured V. All original evidence and physical guards must remain in K even when the chosen representative deliberately realizes only selected constraints.

## Limits and interpretation

These tests do not prove the unbounded theorem, supplied isolation/interlock physics, stationarity, arbitrary-context equivalence, physical source identification, all-filter bounded factorization, or intrinsic categorical/equipment closure. The certificate transport function is an independently executable finite specification fixture, not a hardware driver or production certificate implementation. The categorical CFS comparison and canonical middle are not simulated and are not treated as executable stochastic samplers. No contract closure follows from this PASS.
