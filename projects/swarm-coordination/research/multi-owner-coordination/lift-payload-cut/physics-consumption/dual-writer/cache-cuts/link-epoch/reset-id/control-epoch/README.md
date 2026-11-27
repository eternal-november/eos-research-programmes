# Reset intents, clock projections and actual incarnation capture

See [Reset_Cut.tex](Reset_Cut.tex). This selected-source replay separates
acknowledged reset intent from a native graph reset, and shows why equal
clock values cannot identify an allocation across that cut. It exercises
a source-side capture guard at explicit serial boundaries; the external
epoch and the system-readiness seam are authored, not Gazebo facilities.

Stage the pinned blobs in INPUTS.tsv as a sibling pins directory and run
python3 -B replay.py ../pins. The expected stdout is results.txt.

[Allocation lineage within a world](state-incarnation/README.md) tests the
separate authorized explicit-ID restore path, which needs no global rewind.
