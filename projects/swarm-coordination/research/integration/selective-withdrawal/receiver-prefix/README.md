# Receiver prefix at a handoff

[Proof, source scope and comparison](Receiver_Prefix_Fence.tex). This is an offline source-slice check beside an authored receiver model. It does not modify or run a robot stack.

Materialize the three exact text inputs in [SOURCE.tsv](SOURCE.tsv) in this directory, then run `sh replay.sh`. It verifies their Git blob IDs and the unchanged `receiver.py`. Expected output is [NATIVE.txt](NATIVE.txt) followed by [REPLAY.txt](REPLAY.txt). Lean 4.35.0 checks `PrefixFence.lean`; [AXIOMS.json](AXIOMS.json) records the independent check.
