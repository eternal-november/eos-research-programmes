# Named duty and migrating door writer after restart

Run `set -e -o pipefail; python3 -B replay.py | cmp - EXPECTED.json`.
The standalone archive contains all inputs; the source-file blob pins are checked in replay.py. For Git rehydration, materialize the exact four Open-RMF files linked in the [retained-actuation README](https://github.com/eternal-november/eos-research-programmes/pull/810), and the door_effect.cc.in and door_effect.py from that result. Copy development.js from development-bridge and native_policy.js from its recipient-after-staging/native-two-dock fixture; both are unchanged. Run with Python 3 (SQLite), a C++20 compiler and Node.

Keys of results are future support (steady only / includes migration), first-cut authority report (absent / qualified), and writer (current scoped / both unqualified / scoped hold at chosen gate / stale first snapshot repeated / drop updates after the first). Returned integers are the staging masks that guarantee all obligations; e.g. 3 prepares both shared paths, and 4 prepares only the isolated path. The input journal declares epoch and appointment scenarios; this is not an observation of how stock RMF allocates authority.
