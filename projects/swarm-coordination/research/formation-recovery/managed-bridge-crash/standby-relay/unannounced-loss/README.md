# One standby for an unannounced member loss

[Proof, alternatives and scope](Unknown_Loss_Cut.tex). In a clean copy of the parent `standby-relay` study, follow its input setup and copy `unknown.py` alongside the original `standby.py` (Git blob `b59abb4e385dda5d66bb57d46f59c06dad36ff39`). Then run:

```sh
set -o pipefail
PYTHONPATH=upstream/src python3 -B unknown.py | cmp CUTS.txt -
```

The initial replay lines recertify the 3D parent study. The new checks use exact rational comparisons on the recorded poses; they do not simulate an impact or post-loss plant.
