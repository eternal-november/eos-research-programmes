# SC-CAUSAL-APPOINTMENT: Can two truthful authority receipts authorize the same next act?

Scoped R5, L1–L3 calibration. Independent, cooperative owners A and B keep separate append-only administrative ledgers in this fixture. A's revision 1 allows its shared port to recognize a new issuer; revision 2 ends that administrative power for future appointments without undoing appointments already valid. Operating access to the port is a separate right. B may appoint internally at any time; acting at A's shared port requires the jointly scoped authority.

B actually reads A before recording the appointment. In one order it reads revision 1 before recording the appointment; in the other it reads revision 2. Later, A truthfully reports that its revision 1 allowed recognition, and B truthfully reports the same appointment and issue power in both orders. B can issue the new scoped rescue authorization on its own ledger in both orders. Pairing those two receipts regardless of their causal order would incorrectly let it act at A's port in the second case. A named comparison performed by B resolves the ambiguity without sending the full local history. If B cannot disclose the comparison, there is no local positive proof; neither is there a certificate of historical incompatibility.

The gate separately checks present scoped operating access and the old carrier's actual occupied site in the discrete plant. The historical cut remains good when the older administrative power has expired, but does not authorize a new movement after operating access is withdrawn or while the old carrier remains. The new locally issued authorization is required even when the historical cut is sound. Unrelated inspection runs in all cases.

```sh
python3 replay.py | cmp expected.json -
```

The Python standard-library replay uses separate SQLite files for the two owners and the discrete plant. It enumerates all 32 authored fixtures, and compares a greatest-compatible-cut algorithm on 16,384 seeded causal ledgers with a Cartesian reference. The gate is a local serialization point for plant state, not an arbitration service for the owners' ledgers. No network delays, authenticated transport, continuous movement, dynamic closure under arbitrary privately disclosed evidence, or conflicting preferences are established. A fully informed causal reader gets the same decisions when that disclosure is lawful. This is not an independent mission test, I1/I2 coverage, or R5 acceptance.

See [the statement and proofs](Causal_Appointment_And_Current_Effect.tex) for the exact semantics and prior comparison.
