# Later authority with a physically updated asset placement

[Proof, actual source operations and comparison](Withdrawal_Lineage.tex).
Use the pinned `multi-owner-coordination/named-withdrawal` files from
`e6cfead43ceb1c15d88653c442eb7f762cf09dd4` and the upstream inputs
declared there. The adapter verifies the native fixture and policy
byte-for-byte before adding the two physical old-authority operations.

    python3 -B replay.py /path/to/upstream /path/to/named-withdrawal | cmp expected.json -

The chain records actual source effects, not dispatch commands.
A stale negative is evaluated without executing the proposed move.
Three Lean 4.35.0 statements were checked via AXLE. The matched exact
direct method agrees, and this is not a live hardware or independent test.
