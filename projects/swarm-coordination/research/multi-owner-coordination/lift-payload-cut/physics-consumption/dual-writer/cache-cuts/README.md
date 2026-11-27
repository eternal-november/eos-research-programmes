# Velocity mailbox and sampled command

Run in the dual-writer study with its pinned files:

```sh
python3 -B replay.py /path/to/pins
```

Executes the selected native mailbox and snapshot operations with selected
source writer, consumer, and cleanup paths. No ROS, full scheduler, physics
engine or safety assertions.

[Evidence and limits](Mailbox_Snapshot_And_Physics.tex). For a checked run,
use `set -o pipefail` and pipe the command through `cmp results.txt -`.

[Link recipient epochs](link-epoch/README.md) follow a configured link name
through two scoped changes, separating cached entity, sampled command and
an already staged physics input.
