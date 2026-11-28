# First charged effect

Use Python 3 with NumPy, Git, C++17, and the offline source inputs:

    python3 -B replay_effect_cut.py > actual.txt
    cmp actual.txt REPLAY.txt

From a repository checkout, pass `--source` with the parent #805 radio input files
listed in its [SOURCE_INPUTS.tsv](https://github.com/eternal-november/eos-research-programmes/tree/b3df72334ea67ef6f7e82b63a13255cddc745c19/projects/swarm-coordination/research/integration/shared-admission-core/live-authority/compound-cave-dock/restart/exact-result/mission-lease).
The driver verifies and regenerates the inherited shim; the cave LUT is
not used. Pass `--support path/to/support.py` and `--warehouse directory`
with the #804 [warehouse inputs](https://github.com/eternal-november/eos-research-programmes/pull/804/files).
The test uses the pinned simulator logic, not network or vehicle hardware.

Arms 0 and 4 are the common selector and a source-specific direct equivalent;
arms 1, 2, and 3 are preflight, A-first, and B-first. In the radio witnesses,
tuple keys denote the late debit location (0=A, 1=B, 2=both), policy, and
whether the gap is exactly one second (0=no, 1=yes). Counts in the replay
are exhaustive over the declared sweep, not field rates.
