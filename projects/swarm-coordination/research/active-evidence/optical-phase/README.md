# Resuming an optical receipt stream

After a temporary occlusion, regular falling edges and correct parity can still leave two distinct readings of a continuous UART stream. A restricted alphabet of 84 symbols guarantees recognition of the first complete visible word in at most 21 correctly sampled bits, without changing the 11-bit format. The bound on alphabet size is exact for arbitrary sequences and a receiver that accepts any valid sliding window. One wrong-phase bit error can still produce a false word.

[Proof, source comparison and scope](Optical_Frame_Acquisition.tex). From this directory:

```sh
python3 -B replay.py | cmp results.json
```

The replay uses Python 3.10+ and no dependencies. It enumerates the certificate in `alphabet.txt`; no optimizer is required for verification. Lean 4.35.0 with Mathlib checks the explicit witnesses and the first-wholly-visible-word observation count in `PhaseWitness.lean`. The saved axiom output reports no `sorryAx`.

The [IROS optical link](https://arxiv.org/abs/2208.01710) supplies the wire format and fall-edge timing model. The replay uses synthetic, error-free bit streams, except for an explicit error witness, not camera recordings. It does not certify freshness, physical clearance, worst-case decoding delay, or the independent R1 test.
