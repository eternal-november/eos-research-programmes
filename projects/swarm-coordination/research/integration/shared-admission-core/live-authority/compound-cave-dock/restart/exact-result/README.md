# Exact returned value, charged at the actual receive cuts

Run `python3 result_transfer.py | cmp REPLAY_RESULT.txt -` in the
complete offline archive. It needs Python 3 with SQLite support,
NumPy, Git and a C++17 compiler. A checkout run supplies the two
pinned parent input directories with `--geom` and `--source`.
The experiment pins the old restart adapter as well as its own sources.
All builds and temporary journals are local to the replay.

The finite reference law, conditional effect and artifact boundary
are described in the adjacent TeX. The independent mission is not
used; the direct interpretation with the same format and resources
matches.
