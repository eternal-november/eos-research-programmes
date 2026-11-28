# A native safe-edge change in the fixed-law risk envelope

Run `bash replay.sh > NATIVE.txt && sha256sum -c NATIVE.sha256 && python3 -B check.py NATIVE.txt | cmp - EXPECTED.json`. The bundled source can be reconstructed from the five-column `INPUTS.tsv` (target, repository, source path, commit, Git blob). Dependencies: C++17 compiler, Git, Python 3 and Linux libsqlite3.so.0. `Bound.lean` is standalone under Lean 4.36.0.

This uses the same pinned broker extraction as #840. Y's small packet and the full old retry settle the same fixture key. The database is a receiver-local audit input; it is not made visible to the optional dispatcher. The exact cut and stipulated marginal constraints matter, as explained in the note.
