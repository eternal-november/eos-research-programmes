# Rolling debit after controller replacement

[Proof and scope](Debit_Profile.tex). The same budget can carry different obligations into the next controller. This study gives an exact inherited profile for fixed continuations and a case where a later choice of transmitter needs more.

```sh
python3 -B test.py | cmp REPLAY.txt -
lean DebitProfile.lean
```

For the native broker replay, materialize the six pinned SubT files in [SOURCE.tsv](SOURCE.tsv) as `src0`–`src5` and the exact [existing fixture](https://github.com/eternal-november/eos-research-programmes/blob/e7f48c97497180860b363330fe7daa27e00fe0d4/projects/swarm-coordination/research/integration/subt-relay-debit/replay.cpp) as `upstream_replay.cpp`. Then run `sh native.sh | cmp NATIVE.txt -`. The script checks all seven input blobs.
