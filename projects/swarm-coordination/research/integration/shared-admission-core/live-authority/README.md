# A route grant can outlive its receipt, but not its reservation

**I1 development, not acceptance.** The pinned Open-RMF moderator
really changes reservations and assignments. Warehouse recovery supplies
the physical clearance witness. Their connection to one crossing is
declared by the experiment. The unchanged shared admission checker
and the same-information factored check agree.

[Scope, results and comparison](Live_Authority.tex) ·
[Development freeze](FREEZE.txt) · [Lean kernels](Authority.lean).

## Replay

Use a source parent laid out as in
[the native moderator study](../../blockade-rectification/moderator-replacement/README.md).
The 21 pinned Open-RMF code and header hashes are checked there and
before this compilation. For the pinned warehouse files use the
input layout in [the shared admission study](../README.md). Requires
a C++17 compiler, Eigen, Git, Python 3.10+ and NumPy.

    R=/path/to/eos-research-programmes/projects/swarm-coordination/research
    sh replay.sh /path/to/rmf-source-parent /path/to/eigen3 \
      "$R/integration/blockade-rectification/moderator-replacement" \
      /path/to/warehouse-upstream \
      "$R/multi-owner-coordination/named-withdrawal/in-flight/source-producer" \
      "$R/multi-owner-coordination/named-withdrawal" \
      "$R/multi-owner-coordination/named-withdrawal/in-flight" \
      "$R/integration/shared-admission-core" | cmp expected.json -

The crossing completion is modeled; selected arrivals are fed back to
the native moderator. Nothing here commands physical equipment.
