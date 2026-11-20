# Native strict telescope-algebra recovery

The strict-native-algebra and identity-comparison contextad categories
are isomorphic for the specified split-indexed carriers. Both directions
retain the carrier, its independently supplied normal cleavage and the
directed cartesian map over the two legs. The fold acts on the actual
nested native words, not the packed coefficient-presheaf monad.
This does not address unpresented fibrations, comparison-isomorphism
maps, or an enhanced Eilenberg–Moore 2-category.

Use the Lean subtree from parent commit
`63077f542cca563f28a3b333b74025fc8ecb546a` as `PARENT_LEAN_DIR`, and this
commit's Lean subtree as `CANDIDATE_LEAN_DIR`. Set absolute `LEAN_BIN`
and `PACKAGES` to pinned Lean 4.35.0 and dependency checkouts. Run from
this evidence directory with fresh output paths:

```sh
python3 project-parent.py freeze/parent.json "$PARENT_LEAN_DIR" /tmp/strict-telescope-parent
python3 prepare-overlay.py "$CANDIDATE_LEAN_DIR" /tmp/strict-telescope-freeze
bash /tmp/strict-telescope-freeze/replay.sh /tmp/strict-telescope-parent /tmp/strict-telescope-replay
```

Projection checks 490 parent files; the 15 implementation modules and
two new official probes take the final manifest to 507 files. Replay
checks the pins, rebuilds the project and verifies the ordered 4,879
declaration audits and the 33 official probes. CROSSWALK.tsv gives
source obligations and verified declaration names.
