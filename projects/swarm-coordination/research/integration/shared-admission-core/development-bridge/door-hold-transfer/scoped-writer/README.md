# Scoped door writer cut

This civil simulation fixture extends the pinned-source extraction in the [door-state and retained command replay](https://github.com/eternal-november/eos-research-programmes/pull/810) and the [public history replay](https://github.com/eternal-november/eos-research-programmes/pull/829).

Run `python3 replay.py --source SOURCE --template DOOR_EFFECT_CC_IN --extractor DOOR_EFFECT_PY | cmp - EXPECTED.json`. The six exact blob pins and file names are declared in the script. Standalone evidence archive places these files beside the script, so `python3 replay.py | cmp - EXPECTED.json` suffices. Requires Python 3 and a C++20 compiler. Use AXLE Lean 4.36.0 with Mathlib to check Scoped_Door.lean.

The source command writer is not patched. The fixture supplies its target, authorizes each recurring use, and stipulates the motion integrator. Counts are per-arm agreement on both gates' effective targets, not physical or released benchmark outcomes.
