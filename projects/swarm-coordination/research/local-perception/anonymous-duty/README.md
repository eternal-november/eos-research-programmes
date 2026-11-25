# Anonymous tracks and retained duties

A controller may see exactly where carts are without knowing which carry unresolved work. The model separates the largest load still protected by the controller from the track assignment and from the event that actually settled a duty.

[Model and proof](Anonymous_Tracks_And_Retained_Duty.tex) · [Lean reserve-profile criterion](ReserveProfile.lean)

From this directory, with Python 3 and NumPy/SciPy for the independent matching and MILP baseline:

```sh
python3 -B probe.py | cmp initial.txt -
for f in modes dock_cut coupled_motion pinned_motion reserve_profile milp_compare; do
    python3 -B "$f.py" | cmp "$f.txt" - || exit 1
done
```

The comparison was run with SciPy 1.17.0. Check the finite reserve-profile theorems with Lean 4.35 and Mathlib:

```sh
lean ReserveProfile.lean
```

The positive and negative movement and socket examples are synthetic. They give source-faithful exact decisions in the stated model, not evidence from an independent site or hardware. Matching is exact when the admitted histories are its perfect matchings. The same-information integer solver ties on the larger coupled model.
