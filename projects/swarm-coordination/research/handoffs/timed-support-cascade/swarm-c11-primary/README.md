# Primary warehouse cascade

See Primary_Cascade.tex for law, scope, comparison and outstanding proof obligations. The original.py dependency is an exact local copy of the connected-handoff simulator, making this draft standalone; use a byte-pinned repository dependency on integration.

Run sha256sum -c SHA256SUMS and python3 -B replay.py | cmp results.json. Results include 96 global traces and local receiver histories, with service-cut pending state. This is not a C11 acceptance submission.
