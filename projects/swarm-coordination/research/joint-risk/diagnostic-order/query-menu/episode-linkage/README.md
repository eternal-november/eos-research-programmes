# Risk calibration with lost episode links

[Proof and scope](Risk_From_Unlinked_Episodes.tex) · [model freeze](FREEZE.txt).
At matching assumptions on the fixed menu, unmarked linkage loss
has a quadratic rather than linear cost in the retained fraction.
A single outcome-dependent filter also gives exact nonidentification
despite honest link flags.

    python3 -B replay.py | cmp results.json -

Requires Python 3.10+. The checker uses exact rational probabilities.
This does not measure linkage quality or certify a physical instrument.
