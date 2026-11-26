# An acknowledged route is not recovered progress

Open-RMF's pinned blockade participant deliberately leaves out its last-reached checkpoint when rectifying a reservation mismatch. That makes initial repair traffic identical for two participants on the same route, with the same readiness, one still at checkpoint zero and one already at checkpoint two. Once the reservation matches, the latter participant reports the difference. Its report still cannot recover the moderator's recorded progress unless the current assignment covers checkpoint two.

[Proof and scope](Rectification_And_Progress.tex). The executable compiles the selected original mismatch and reached handlers with inert data structures. It does not synthesize the assignment, simulate geometry or claim a fleet safety failure.

Save the pinned [Participant.cpp](https://github.com/open-rmf/rmf_traffic/blob/4da6ff65e811038f73c6ca4e9ea3880a9af5938f/rmf_traffic/src/rmf_traffic/blockade/Participant.cpp) and [Moderator.cpp](https://github.com/open-rmf/rmf_traffic/blob/4da6ff65e811038f73c6ca4e9ea3880a9af5938f/rmf_traffic/src/rmf_traffic/blockade/Moderator.cpp). With Python 3 and a C++20 compiler:

    python3 replay.py Participant.cpp Moderator.cpp > actual.txt
    diff -u results.txt actual.txt

The [full native in-process replay](moderator-replacement/README.md) runs the geometry and assignment logic, producing the constrained and unconstrained ranges instead of supplying them.
