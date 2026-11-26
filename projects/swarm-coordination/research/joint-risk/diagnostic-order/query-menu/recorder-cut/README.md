# Recorder timestamps and episode identity

[Proof and source boundary](Recorder_And_Episode_Identity.tex).
A selected native recorder callback can send identical writer inputs
for two valid assignments of payloads to earlier acquisition episodes.
Both clock modes are replayed. A separate exact check compares all
unconstrained residual matchings with the sharp empirical interval.

Supply the pinned source files in [SOURCE.tsv](SOURCE.tsv) with their
listed short names. Run:

    sh replay.sh /path/to/upstream | cmp results.txt -

Requires Python 3 and a C++17 compiler. The replay uses stubs for ROS
and a writer spy; it does not make claims about actual transport order,
storage plugins or population risk.
