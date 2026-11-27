# Typed callback and station evidence

Read Typed_Callback_And_Station_Evidence.tex for the source-to-evidence
map, trust assumptions, and meter/callback/consumption distinctions.

Populate up/ from SOURCE.tsv (destination, repo, commit, source path,
Git blob hash). Then:

    sh run.sh up | cmp expected.json -

The shell requires a C++17 compiler, Python 3, SQLite, NumPy, NetworkX,
and Git. Source files are pinned; the build exposes native methods
without replacing their communication semantics. Tapes are from a
controlled synchronous civil fixture. Rejections fabricated only in
the offline tape tests check the generated normalizer, not a live target.

Across 16 native station cases, every fresh/stale checkpoint pair
has an identical radio tape, while the stale checkpoint cannot consume
a delivered result. With identical application callbacks at the early
cut, routing the budget observation into the old receive ledger rather
than the independent verifier changes whether the old named packet can
arrive. The typed source taps retain the difference before the commit.
