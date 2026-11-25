# Shared two-cut recovery

[Result, proof and limits](Shared_Recovery.tex) · [scope fixed before branch testing](FREEZE.txt). One exact local policy synthesizer uses selected native traces from two different resource types: an occupied warehouse berth and a spent transmission window. Treat the direct tie and extra losing history as part of the result.

To replay from a clean copy, use the complete Space archive and run **sh replay.sh | cmp replay.txt -** (Python 3, NumPy, C++17). The archive includes the pinned RWARE source/license/helpers from the simultaneous-port and source-and-return studies and the archived SubT relay-debit sources and license from the neighboring study. To reconstruct manually, copy those exact dependencies and the SubT study's replay.cpp/extract.py under subt/, then supply the native files named in that study. The wrappers verify the original blobs. The Lean source checks the abstract local-information criterion, not the runtime.

A [separate replay with a queued old attempt](../shared-retire-cut/README.md) checks whether the resource read remains valid through the next commitment while unrelated work continues.
