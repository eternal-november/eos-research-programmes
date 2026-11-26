# Independent unknown offsets make an exact risk cap hard

The [preceding ordered-clock result](../README.md) gives a polynomial exact worst failure count with one shared unknown offset. The [new proof](Private_Clocks_And_Joint_Risk.tex) shows that allowing a separate unknown offset per source makes the cap check coNP-complete, even with isolated blocks of two episodes, uniformly bounded residuals, and feasible full linkage at every offset. The reduction encodes a Boolean variable in which of two offset bands can move a failure into a clause's first episode. It uses the classic [NP-completeness of satisfiability](https://www.cs.umd.edu/~gasarch/BLOGPAPERS/Karp.pdf); the replay checks exact counts independently.

The boundary is scope of the unresolved offset: known offsets, a single common offset, or a fixed number of independent shared groups retain polynomial exact upper counts. Pooling individual edges across a private offset is not valid. This is about complete synthetic streams under a declared acquisition law, not a measured timestamp implementation.

    python3 replay.py > actual.json
    diff -u results.json actual.json

[Lean](PrivateClockGadget.lean) verifies the continuous real inequalities for sorted and swapped pairs, block isolation, polarity, and the equivalence with Boolean clause satisfaction for the abstract literal relation. The polynomial reduction and padding are in the TeX proof. Run the Lean file under Lean 4.35.0 with Mathlib; the [axiom audit](AXLE_AUDIT.txt) contains no placeholder axioms.

The [certificate follow-up](coverage-audit/README.md) bounds the hard case from both sides and states when a bound cannot settle a cap.

The [LinuxPTP freshness replay](ptp-freshness/README.md) checks a concrete source boundary: a new ingress time does not, by itself, certify a new offset estimate.

The [historical query follow-up](query-work/README.md) gives the exact cost of finding a short clock certificate even for one fixed risk cap.
