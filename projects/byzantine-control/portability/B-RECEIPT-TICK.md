# When do staging and expiry jointly break a receiver read?

**BC-PORT-RECEIPT-TICK**

The two edits interact in B’s actual timed receiver code: delaying a fresh maintenance record or advancing the old record’s expiry tick is harmless alone, but together they leave a paid local read without a value. This is a receiver-level counterexample from an explicitly supplied cut, not a reachable counterexample to the full B handoff.

## Same receiver and old record in all four arms

Use the B receiver and raw record implementations at repository revision e1348964f73704212d2d8b48d5982a5ed600a2ff. Follow [Receiver](https://github.com/eternal-november/eos-research-programmes/blob/e1348964f73704212d2d8b48d5982a5ed600a2ff/projects/byzantine-control/portability/rx_product.py#L42-L90) for admitted oscillator phases and [record arbitration](https://github.com/eternal-november/eos-research-programmes/blob/e1348964f73704212d2d8b48d5982a5ed600a2ff/projects/byzantine-control/portability/input_lifecycle.py#L203-L239) for why a running decrement precedes a staged receipt. Both branches use an installed lifetime-512 record, the same origin-owned funding and fixed lane identity, and a prior committed value 441 with one decrement left. The checker builds that record state by committing and servicing 511 decrements. It then supplies the independent oscillator phase and a new already-admitted payload at the receiver staging interface. It does not replay the common physical prefix, the transmitter/flight/parser path to that interface, or the positive successor bank.

Let Δ = 64/2²⁰ q be the local commit delay. The new word 913 is staged at 0 or 2Δ. The next decrement opportunity is at 5Δ or 1.5Δ, using the same admitted oscillator rate. The diagnostic paid capture is fixed at 3.25Δ, not asserted to be a real mission deadline.

## Four arm result

| Staging | Decrement opportunity | New word commits | Paid read |
| --- | --- | --- | --- |
| 0 | 5Δ | Δ | 913 |
| 0 | 1.5Δ | Δ | 913 |
| 2Δ | 5Δ | 3Δ | 913 |
| 2Δ | 1.5Δ | 3.5Δ | unavailable |

In the last arm the decrement starts before fresh ingress and holds the commit aperture until 2.5Δ. When it completes, the old word expires. It then takes one more commit delay for the new word to become visible. Every arm reads 913 by 4Δ. The exact calculation agrees with executed native receiver transitions in both bank orientations. The same outcomes held in all 18 checked sets of four runs varying the delayed staging time from 1.9 to 2.1Δ and early tick from 1.4 to 1.6Δ. The margins are strict; no simultaneous-event ordering convention is responsible.

## Proof reuse and scope

Let a denote staging time and m the time the running decrement starts, both in units of Δ. On these strict-order branches commit occurs at a+1 unless m<a<m+1, when it occurs at m+2. This uses the actual arbitration rule: a running decrement keeps its own claim, whereas a subsequent clock opportunity queues behind an already-staged receipt. A contextual proof can retain the pending decrement and join the two schedules on the same clock and record. The direct proof obtains the same condition by tracking the same pending claim. Both can keep the receiver proof unchanged and both must discharge the same timing relation. Neither needs separate proofs for the four arms.

A loss of the full B guarantee would need a reached joint execution with the chosen staging/expiry phases at an actual required read and no valid sibling supplying that read. The original [positive receiver lease](https://github.com/eternal-november/eos-research-programmes/blob/e1348964f73704212d2d8b48d5982a5ed600a2ff/projects/byzantine-control/portability/RECEIVER-LEASE.md) has separate advance priming, overlap and same-bank read hypotheses. Also, B’s ordinary actuator maintenance SEND is not this record’s expiry tick. No evidence here equates their paths or makes the ordinary SEND shift an admissible edit of this test.


The [synthetic handoff comparison](HANDOFF-RECEIPT-REUSE.md) asks a separate question with a fixed maintenance schedule. Here the actual receiver runs, but both schedules are supplied at its boundary.

## Reproduction

Run `python3 -B b_receipt_tick.py` from this directory with Python 3.12, without `-O`. The [checker](b_receipt_tick.py) prints the nominal traces and number of perturbed sets, and asserts agreement with the exact timing calculation. This is a finite regression, separate from the timing argument above.
