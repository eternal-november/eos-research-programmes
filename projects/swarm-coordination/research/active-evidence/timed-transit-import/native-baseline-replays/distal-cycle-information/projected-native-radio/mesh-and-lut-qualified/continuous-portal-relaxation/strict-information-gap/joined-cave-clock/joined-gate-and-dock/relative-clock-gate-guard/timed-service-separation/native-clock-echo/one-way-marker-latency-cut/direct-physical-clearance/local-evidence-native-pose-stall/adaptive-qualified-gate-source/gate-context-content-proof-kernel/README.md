# Context and content contracts for one immutable cave gate duty

This is an executable proof scaffold for the held-in gate worker.
`kernel.py` is the independent small semantics; `native.py` is the
pinned actual worker used in the live-authority cave replay.
The operational profile check and concrete trace check are distinct.

```sh
python3 -B profile_checks.py | cmp - PROFILES.json
python3 -B verify.py | cmp - EXPECTED.json
```

Python 3 and SQLite. This verification is not an implementation of the
general Interactad calculus: its domains and operations are explicitly
restricted to one fixed semantic gate duty.
