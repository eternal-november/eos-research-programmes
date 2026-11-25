# Joint clock calibration and incomplete transfer observations

[Model and proof](Common_Clock_Transfer_Matching.tex) · [Lean arithmetic](ClockMatch.lean)

```sh
set -o pipefail
python3 -B offset_match.py | cmp replay.txt -
python3 -B partial.py | cmp partial.txt -
python3 -B check.py | cmp cert.txt -
lean ClockMatch.lean
```

`cert.py` regenerates `cert.json` using SciPy 1.17.0. The separate checker uses exact integer duals and rational clock cells. The measured-data citation motivates the provenance gates; there are no observed dataset values in these fixtures. No independent transfer is claimed.
