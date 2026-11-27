# Sender-scoped receive allowance

The selected broker compares receiver occupancy with the *sending* radio's threshold. A different sender can reverse which of two report orders works, even with the same receiver, contents and offered byte count. The positive case is a standard earliest-due-date reduction, with cumulative bytes as the processing coordinate.

- [Source cut, proof and limits](Sender_RX_Allowance.tex)
- `SenderRx.lean`: exchange and model-bound witness checking with Lean 4.35.0 + Mathlib.
- Materialize exact pinned inputs from `SOURCE.tsv`; then run `sh replay.sh INPUT > actual.json` and `cmp expected.json actual.json`. Requires Python 3, Git and C++17.

Native callbacks and debits: 1,296 rows. Multi-receiver and uncertainty extensions are model checks, not new native or held-out missions.
