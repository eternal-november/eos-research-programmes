# Physical completion and a carried radio receipt

The old order actually has to finish before the wrapper emits its report.
Trying to stage an extra pickup from only the warehouse's view can spend
the radio room needed for that report. Considering only radio capacity
can instead consume the pickup that would let the order finish.

[Model, proof and comparative limits](Station_And_Receipt.tex).
Install the pinned source files named in [SOURCE.tsv](SOURCE.tsv); then run:

    sh replay.sh /path/to/inputs | cmp expected.json -

Git, Python 3 and C++17 are required. The replay checks 144 selected-source
fixtures. Source linkage is authored, with fixed authority, clock, direct
path and receiver in the envelope. No claim of field transport or I1 acceptance.
