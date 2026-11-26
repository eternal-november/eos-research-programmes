# Optical relay formation after a stopped-robot fault

[Model and proof](Opaque_Relay_And_Switching.tex). A single opaque
stopped robot creates an exact aperture cutoff, a one-versus-two relay
separation, and a case where two valid service positions cannot be
joined without losing optical service. The exact trajectory result
assumes an ideal bounded-speed point kinematic model with an inflated
body clearance, not a radio or packet-delivery guarantee.

Python 3.10+, standard library only:

    python3 -B replay.py | cmp expected.json -

OpaqueRelay.lean: four checked lemmas with Lean 4.35.0 and Mathlib
(no sorryAx). The polar path length argument is in the TeX proof.
This is a scoped supporting R6 result, not a reproduction of the
published distributed MPC or full R6 discharge.
