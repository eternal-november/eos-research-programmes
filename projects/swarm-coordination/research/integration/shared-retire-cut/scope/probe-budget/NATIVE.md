The existing shared-retire-cut source adapters are pinned to merged PR 482,
commit 827441577998474e5b9a33683ff64a7f1955f18b. The five dependency files
in adapter.sha256 were independently byte-compared to the repository at
that commit. Use those exact files and the upstream directory specified by
their SOURCE.tsv. The Space archive includes those fixtures and upstream
files with their licenses. Run:

    python3 replay.py | diff -u results.json -
    sh native.sh ../adapter ../upstream | diff -u native-results.json -

The foreground C++ driver is built on a temporary directory. Python reads
the rescue action results for each held old scope in each adapter. The
selected original holds produce the masks {right} and {left}, with old
progress and an outstanding old duty in both cases. The inspection layer,
cost and fault budget are imposed after that projection. The result does
not assert that either stock system exposes that inspection interface or
that it meets a physical deadline.
