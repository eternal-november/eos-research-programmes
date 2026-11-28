# Joined first-effect adapters

Run the offline source bundle using Python 3 with NumPy, Git and C++17:

    python3 -B joined_effect.py | cmp - REPLAY_JOINED_FINAL.txt

From a checkout, use the exact source and RWARE inputs described in the
[parent first-effect replay](../README.md). The same `--source`,
`--warehouse` and `--support` flags apply. The launcher verifies the
parent selector and source extractor.

Each witness key is (later radio pattern, later occupancy pattern,
policy). Patterns 0 and 1 block A and B respectively; 2 means both
and 3 means neither. Policies: 0 = joined selector; 1 = radio only;
2 = cell only; 3 = factored direct join; 4 = stale preflight;
5 = joined selector with an intervening native re-entry.
