# Corridor observation and a live report rebind

The authored directed motion system supplies the local blocked
arm observation; a native timed broker replay checks actual command,
old report, optional expenditure and independent report effects.
[Scope, comparison and timing proof](Corridor_Live_Rebind.tex).

Use the timed source producer at main revision
c6b9d3799256ac09f04c9d211baea14bc15f4ecf and the pinned upstream
inputs declared in SOURCE.tsv. Python 3 and C++17:

    sh replay.sh /path/to/upstream /path/to/timed-source-producer | cmp expected.json -

Four abstract lemmas in AccessCut.lean were checked in Lean 4.35.0
via AXLE. The exact matched planner ties. No independent mission,
field evidence or acceptance of I2 is claimed.

[Source-local preflight](source-preflight/README.md) relaxes the geometry-to-radio correlation and checks actual active observations. [Command-overlap control](command-overlap/README.md) shows when the shared physical ledger invalidates otherwise timely evidence. Both exact matched references tie; neither consumes the independent case.
