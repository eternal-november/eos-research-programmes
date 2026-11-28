# Public histories, delayed reports and expiring hold comparison

After unpacking the Space bundle, verify `sha256sum -c SHA256SUMS`, then run
`set -o pipefail; python3 -B public_frontier.py | cmp - PUBLIC_EXPECTED.json`.
Requires Python, C++20 and Node. Repository materialization flags:
`--source`, `--template`, `--extractor`, `--policy`, `--model`.
The tester freezes all capability arms and tests actual decisions using the
unchanged core from #826 and importer from #827.
