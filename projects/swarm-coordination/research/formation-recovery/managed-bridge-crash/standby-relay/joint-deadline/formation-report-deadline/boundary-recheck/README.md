# Reuse a formation constraint proof without retaining the interior graph for every decision

The [proof](Boundary_Proof_For_Live_Changes.tex) gives an exact receiver for replaceable difference constraints at declared endpoints. Retain the tight shortest-path bounds between those endpoints. The receiver handles whole batches, and an accepted endpoint assignment can be lifted to the original constraint graph. Any changed retained entry can be detected by a single reverse-edge requirement, so weakening the summary is not safe for this entire query family.

In the replay, two local gap changes each pass but fail jointly against the retained total-span constraint. A separate control shows why storing a replaceable old constraint inside the frozen base wrongly rejects a lawful relaxation. The replay compares with the full graph and measures edges read per decision, not total verification cost.

The underlying [simple temporal network closure](https://cse.unl.edu/~choueiry/Documents/DechterMeiri-AIJ.pdf) and [incremental propagation](https://cdn.aaai.org/ojs/13417/13417-40-16935-1-2-20201228.pdf) are established direct mechanisms. This uses them to make the interface and its exact retention obligation explicit for the [formation deadline model](../README.md). No physical or independent transfer test is claimed.

    python3 replay.py > actual.json
    diff -u results.json actual.json
