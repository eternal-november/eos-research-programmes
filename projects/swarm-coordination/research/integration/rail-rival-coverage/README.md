# Rail rival reports and queue promotion

[Source boundary and bounded model](Rival_Report_And_Queue_Promotion.tex). Source version: SUMO 1.26.0 commit `fa7df22d7f1c4ae245192ecc32410a49f1ffb2a3`.

Fetch the exact `MSDriveWay.cpp` and `MSRailSignal.cpp` from `src/microsim/traffic_lights`, and `MSLink.cpp` from `src/microsim`. Save the three under their basenames in a source directory. The extraction verifies the Git blob hashes.

```sh
python3 -B extract.py /path/to/pinned/sources native.inc
g++ -std=c++17 -O2 -Wall -Wextra -pedantic run.cpp -o check-rivals
./check-rivals | cmp - native-results.txt
python3 -B model.py | cmp - model-results.json
```

The Space archive includes the generated include for offline execution. The native harness supplies authored geometry, occupancy and approach predicates; it does not run a full SUMO network.
