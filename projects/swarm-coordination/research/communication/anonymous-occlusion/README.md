# Passive tracks and named duty after an occlusion

Two exact anonymous detections do not automatically re-identify a robot.
A coupled collision-safe motion test rules out some exchanges admitted by
independent track matching. Once both exchanges are physically possible,
fresh anonymous frames need not tell the original names apart.

[Motion proof, evidence, and comparisons](Anonymous_Track_Recovery.tex) · [Lean](Identity.lean).

    python3 -B replay.py | cmp expected.json -

Python standard library. Geometry checks use bounded polygon comparisons and
explicit floating-point tolerance. This is a held-in model, not a detector
benchmark, RF result, or independent non-radio substitution test.
