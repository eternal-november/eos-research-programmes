# Declared history envelope audit

Coverage and effect checks for the existing [radio supplier change](../live-clearance-generation/radio-bounded-handoff/suffix-supplier-change/README.md) and [MRWS ordered classes](../ordered-retained-classes/README.md) development cases.

[Proof, two omitted-history witnesses and limits](Declared_History_Envelope.tex).
The two omission mutants leave the old join's binding set unchanged and
make a previously refused action pass. Checking the declared history
names refuses both exports without treating the erased row as
unreachable. Independently checking effect evidence rejects corrupt
records with correct names. No new plant run is claimed here.

Supply an input directory with the files named in [PINS.json](PINS.json),
copied byte-for-byte from their paths at the stated repository commit.
The pins bind the two existing outputs, runners, upstream manifests and
unchanged core. Run with Python 3, without optimization:

    python audit.py /path/to/inputs | cmp expected.json -

To regenerate the original selected-source outputs, follow the two
linked replays. This audit has 138 declared histories and 556 negative
controls, plus two explicit before/after decision witnesses. It does
not certify that the input domain exhausts either native application,
make a live controller observation available earlier, or close I1.
