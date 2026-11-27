# SC-CAUSAL-ORDER-REFINEMENT: Does a frozen proof survive a change in dependencies?

An old proof that kept only the least and greatest valid historical cuts is reusable when added dependencies only rule out old cuts. It must still be checked against the new dependencies. An appointment that now requires an excluded withdrawal can make a joint rescue impossible even when both grants remain valid somewhere. Deleting a dependency is different: two rules may have had identical cuts only because the dependency held. The frozen proof may no longer distinguish them.

The exact boundary is that all new cuts, restricted to the old events, must still be valid old cuts. This covers fresh appends and stronger order, but not removal of old reachability. The result concerns admissibility of historical witnesses, not current permission, physical clearance, or runtime discovery of dependencies.

```sh
set -o pipefail
python3 replay.py | cmp expected.json -
```

[Statement and proof](Causal_Order_Refinement.tex). The replay enumerates the boundary and a discrete appointment and withdrawal fixture. No independent mission test or R2 acceptance.

The [Lean checks](CutTransport.lean) cover old closure equivalence, transport under order inclusion, and a separating old-equivalent pair when an edge is lost, on a common event type. All three pass in Lean 4.35.0 with no axioms. The paper and replay cover the additional event and projection cases.
