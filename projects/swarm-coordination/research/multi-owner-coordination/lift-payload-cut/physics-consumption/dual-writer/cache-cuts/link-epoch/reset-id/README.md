# Entity identifier reuse across a Gazebo world reset

[Technical note](Reset_Recipient_Identity.tex). In the pinned allocator,
an id already removed before reset need not contribute to the restored
allocation counter. An entity present immediately before reset is a
different case, even when reset removes it. This distinguishes a body
allocation from its reusable numeric identifier.

Stage the inputs listed in INPUTS.tsv in a sibling pins directory. Run
python3 -B replay.py ../pins and compare stdout with results.txt. This is a
selected-source graph replay, not a full Gazebo/transport run. The authored
archive example demonstrates a receiver condition, not a stock receipt API.
