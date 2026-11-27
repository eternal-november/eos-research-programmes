# The final ordered queue can lose an earlier cue's reference

[Technical note](AsOf_Dispatch.tex). After two actual native deliveries,
both histories have the same ordered current queue and the inspector
has the same complete local observation history. Yet the inspector
must make opposite turns to finish in its two remaining steps.
A source record naming the assignment at the earlier probe cut
distinguishes them. The new assignment at the same slot does not.

The simulator journal records native motion, dispatch and observation
provenance in one local transaction. Both staged-operation rollback
and a lost reply after durable commit were tested. This is simulated
source-state atomicity, not atomicity of an external physical actuator.
The authority of the local journal and scope binding are assumed;
no deployed transport, radio deadline or independent mission has been
tested.

Materialize `ASOF_INPUTS.tsv` here, or use the [source-complete Space
archive](https://chatgpt.com/space/page_f5a09a52f6b881919b10d91ecf2caa80).
Run `sh run.sh | cmp expected.jsonl -` (archive names `run-asof.sh` and
`asof.jsonl`). Python 3, NumPy, Git and SQLite WAL are required.
