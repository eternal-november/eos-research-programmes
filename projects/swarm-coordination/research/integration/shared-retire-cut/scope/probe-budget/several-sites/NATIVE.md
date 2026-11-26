Use the held-scope fixtures pinned to PR 482, commit
827441577998474e5b9a33683ff64a7f1955f18b, and their upstream inputs
named by SOURCE.tsv. The archive includes both sources and licenses.
The five local adapter files are verified by adapter.sha256, and the
upstream input verifier checks Git blob identities.

    python3 replay.py | diff -u results.json -
    sh compound.sh ../adapter ../upstream | diff -u compound-results.json -

The compound test executes clean independent fixture runs for all combinations.
The exclusion of one cross-resource world is imposed by the development test;
it is not attributed to the two sources or estimated from their results.
