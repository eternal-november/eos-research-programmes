# Bearing ambiguity before a sampled path has enough lateral extent

[Proof and limitations](Bearing_Evidence.tex). Obtain each source path in [SOURCE.tsv](SOURCE.tsv) at [the dataset pin](https://github.com/Harvard-REACT/WSR-Toolbox-Dataset/tree/7c8cb67c8dff9553e39f65552c0de4bf427ba42c), locally named as in the first column. The listed Git blob IDs are checked before reading coordinates. The source data are not copied into this study.

```sh
set -o pipefail
python3 -B replay.py | cmp REPLAY.txt -
lean ArcBounds.lean
```

Lean 4.35.0 with Mathlib checks supporting arc facts. This compares an authored phase compatibility model on physical recorded geometry, not an actual bearing-estimator replay.
