# Command range and retained slew at a joint-limit change

Reconstruct `SOURCE.tsv` (target, repository, commit, repository path, blob) under `source/`, or use the complete archive. C++17 compiler, Git and Python 3 are required.

```sh
bash replay.sh > NATIVE.txt
sha256sum -c NATIVE.sha256
python3 -B check.py NATIVE.txt | cmp - EXPECTED.json
```

`Handoff.lean` is standalone in Lean 4.36.0. The harness supplies one velocity-only joint, checks desired output and does not emulate the hardware write or runtime parameter update.
