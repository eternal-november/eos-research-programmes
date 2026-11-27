# The random-source footprint of SubT dispatch

Two disjoint sends can swap simulated outcomes when they swap visits
to a shared random-number stream. A receive-capacity rejection still
consumes a packet mark; a transmit-capacity rejection does not.
The matched attempt-indexed replay preserves physical marks under
reordering. This is a selected-source replay, not a channel law.

[Scope, native code and comparison](Stochastic_Footprint.tex).
Use [SOURCE.tsv](SOURCE.tsv) to prepare the pinned inputs, then:

    sh replay.sh /path/to/inputs | cmp expected.txt -

Requires Git, Python and C++17. The modified fixture supplies specific
values at the existing draw hook; the pinned native functions are not
modified. No production RNG implementation or transport guarantee.
