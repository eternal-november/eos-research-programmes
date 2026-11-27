# A truthful shelf flag still needs a known reference

[Technical note](Native_Observation_Cut.tex). In the pinned RWARE source,
the optional normalized dictionary observation casts fractional coordinates
to integers. Two distinct interior poses can give the same full local
input and need opposite first turns to reach a bay in two steps. The
normalized flat path retains the location distinction, as does the
unnormalized dictionary path.

With the ambiguous observation, actual motion reveals a requested-shelf
flag. The exact completion bound in the selected two-pose case is five
actions when the producer-to-shelf reference is known and eight when it
is not. A real unrelated delivery changes the queue that supplies the
flag. When that action can mark either shelf, the same positive flag
can come from opposite poses.

This selected native replay checks the observation bodies and the
one-mover step graph, not all observation modes or warehouse conflicts.
The package defaults to flat and unnormalized. No upstream change was made.
Materialize `SOURCE.tsv` beside the harness or use the [Space
source-complete archive](https://chatgpt.com/space/page_f5a09a52f6b881919b10d91ecf2caa80).
Run `sh run.sh | cmp expected.json -` (Python 3, NumPy and Git).

[Delayed cue reference](timed-reference/README.md) shows when a later
binding can still interpret a local flag that has already left view.
