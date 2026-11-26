# Adaptive verification of several required sites

With exactly k usable sites in every possible world, a fixed order requires one check per potentially usable site. A policy limited to B adaptive checks can cover up to binomial(B+1,k) minus one sites, and this bound is attained.

[Proof and scope](Adaptive_Verification_Of_Several_Sites.tex) · [Exact replay](replay.py) · [Recorded results](results.json)

Run python3 replay.py and compare stdout with results.json. This is an abstract development model, not a test of multiple-site operations on the two native adapters.

The optional compound control replays two separately pinned resource adapters with a declared coupling between their old scopes. For dependencies and the command, see NATIVE.md.

[Joint risk under a hard read budget](joint-risk/) gives sharp failure bounds for known joint laws and unknown coupling with fixed single-resource marginals.
