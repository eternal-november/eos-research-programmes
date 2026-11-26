# Clock-bound occupancy gaps and named proof reuse

**I1 development only.** The reuse task is a fixed integer-time use
shape at a qualified resource. Three verdicts distinguish a witnessed
possible conflict, a known-safe use, and missing horizon evidence. The
same-information direct tick check and the shared admission core agree.
No field calibration or independent mission result is claimed.

[Model and comparison](Clock_Bound_Occupancy.tex) ·
[Development scope](FREEZE.txt) · [Lean kernels](ClockBinding.lean).

Use Python 3.10+, NumPy, SciPy, Git and a C11 compiler. Prepare the pinned
warehouse inputs from [the shared core](../README.md) and the two
LinuxPTP source files from [the notification replay](../../../joint-risk/diagnostic-order/query-menu/recorder-cut/recorder-clock/three-stream/ordered-clock/private-clocks/ptp-freshness/notify-historical-bound/README.md).

    R=/path/to/eos-research-programmes/projects/swarm-coordination/research
    P=joint-risk/diagnostic-order/query-menu/recorder-cut/recorder-clock/three-stream/ordered-clock/private-clocks/ptp-freshness/notify-historical-bound
    sh replay.sh /path/to/warehouse-upstream \
      "$R/multi-owner-coordination/named-withdrawal/in-flight/source-producer" \
      "$R/multi-owner-coordination/named-withdrawal" \
      "$R/multi-owner-coordination/named-withdrawal/in-flight" \
      /path/to/pinned-linuxptp "$R/$P" \
      "$R/integration/shared-admission-core" | cmp expected.json -

The physical use tape is sampled from the native fixture, including
the follow-on commands. The clock transport/error and scope-binding
laws are declared and not validated by the replays.
