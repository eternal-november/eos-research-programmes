# Selective withdrawal of a reserved movement

The proof and assumptions are in `Selective_Withdrawal.tex`.

- `python3 compare.py` runs the synthetic two-movement comparison against
  a separate direct tick simulator. The unchanged receiver is included.
- `python3 native_replay.py` checks selected exact Java methods with a small
  harness. Use OpenJDK 21. It needs the three pinned upstream files listed in
  the script, beside it. The Space replay archive includes those exact bytes.
  Do not launch a live dispatch or a device to reproduce this test.

This is a development case, not an independently selected mission or an
implementation of a selective withdrawal operation in openTCS.
