# Native-source development replay for inspection and exact audit

Run with a working C++17 compiler, Node, Python with NumPy and SQLite, and Git:
`set -o pipefail; python3 -B native_bridge.py | cmp - NATIVE_BRIDGE_FINAL2.json`.

The Space bundle includes the exact pinned excerpts and wrappers; run
`sha256sum -c SHA256SUMS` before live replay. In the repository, use
`--source`, `--warehouse`, `--support` and `--journal` for those
materializations. The parent modeled sources are located by default
(`--model`, `--expected-model` override them). The test first compares
the extracted algorithm with the existing direct comparator, then reruns
each selected policy in the native-source fixture. Lean source documents
separate sufficient adapter obligations for generalization.
