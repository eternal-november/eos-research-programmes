# Hearing the cue versus still having time to recover

[Proof and channel interface](Listening_Cost.tex). Missing the cue after a stationary read can cost a tick even when the fastest no-read recovery is unchanged. The safe choice to attempt the read is made before it consumes the tick.

From the [pinned optical rendezvous study](https://github.com/eternal-november/eos-research-programmes/tree/13a97f5351ddaa3dfebb74b7b08e96cc167e496e/projects/swarm-coordination/research/communication/optical-rendezvous), place `replay.py` here as `optical_source.py` and `receiver_policy.json` under its original name. Both are digest checked and present in the Space archive. Run `python3 -B replay.py | cmp replay.txt -`. The replay checks the model and counterexample, not acoustic recordings or physical deployment.
