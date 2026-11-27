# Capture cadence as a physical departure constraint

[Frame_Cadence.tex](Frame_Cadence.tex) separates waiting at rest for
a usable frame from processing that frame while preparing the maneuver.
The nominal 20 Hz gate can miss the required capture phase even with
zero processing delay. A controlled force call is a model comparison,
not a claim about permissions or deployed frame scheduling.

From the parent raster-validation root, with its sensor/radio/motion.py
materialized from the existing source manifest, run
python3 -B cadence/cadence.py and compare to cadence/expected.json.
The Space archive contains the exact parent.
