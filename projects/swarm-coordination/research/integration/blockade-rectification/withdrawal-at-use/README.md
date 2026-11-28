# Open-RMF reservation withdrawal and physical clearance

The selected source files and Git blob checks are listed in SOURCE.tsv. Use the same native Open-RMF source and Linux C++17 compiler as the parent moderator-replacement test. The complete archive includes the pinned source files and Eigen headers; from its root:

```sh
set -e -o pipefail
sh study/replay.sh . eigen3 | cmp - study/EXPECTED.txt
python3 -B study/crossing.py | cmp - study/MODEL.json
```

The eleven output columns are allocator/participant renewal (unchanged, rebook, replacement), whether the readiness was already withdrawn before the sample, B boundary (approaching, reached midpoint and ready to leave, actually reached exit), delivery policy (raw, serialized current-source read, cached earlier read), withdrawal after the read, old copy already accepted before withdrawal, active reservation ID, delivered candidate ID, accepted readiness, A range end, B range end. Runtime motions and physical truth are authored; exact native source calls are in replay.cc. The three-arm native comparison and subsequent motion admission are distinct.

The Git copy retains the model, fixture, manifest and checked results; use SOURCE.tsv and any compatible Eigen 3 include for manual reconstruction. The standalone archive contains the exact dependency bytes used for the clean check.
