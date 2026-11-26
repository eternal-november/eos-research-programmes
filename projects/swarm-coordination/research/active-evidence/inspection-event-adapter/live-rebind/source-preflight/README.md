# Actual source preflight without a geometry-to-radio oracle

[Mechanism and limits](Source_Preflight.tex). Actual native probe outcomes
and local cell observation are kept separate. Stable paths, command scope,
clock and one-sided erasure are explicit. Same-information direct ties.

Inputs are SOURCE.tsv and the timed-source-producer and live-rebind
directories at main 804f0cc9b1f38044e63be901a49bd945636334a3:

    sh replay.sh /path/to/upstream /path/to/timed-source-producer /path/to/live-rebind | cmp expected.json -

Both borrowed code files are hash-checked. Requires Python 3 and C++17.
QualifiedProbe.lean was checked under AXLE Lean 4.35.0.
