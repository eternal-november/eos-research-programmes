# From a clock notification to a historical offset bound

The [note](Notify_And_Historical_Clock_Bound.tex) follows the [polling counterexample](../README.md). The pinned LinuxPTP synchronization path does not emit a time-sync notification after a failed estimate, even though a poll can report new ingress with an old offset. It can emit when unlocked, and a jump can emit with ingress cleared to zero. These are selected-code results with inert clock operations and transport.

Even a fresh observation is not a historical certificate. Under a separately justified drift bound, a constant acquisition-epoch offset, and timed measurement error bounds, the note proves the exact offset interval available at admission. The synthetic example needs a timely older observation as well as a fresh one to settle the query.

Save the pinned [clock.c](https://github.com/richardcochran/linuxptp/blob/227bbd4715bf4cb735be4947e987032f41457585/clock.c) and [tsproc.c](https://github.com/richardcochran/linuxptp/blob/227bbd4715bf4cb735be4947e987032f41457585/tsproc.c). With Python 3, a C11 compiler and SciPy:

    python3 replay.py clock.c tsproc.c > actual.txt
    diff -u results.txt actual.txt
    python3 calibration.py > actual.json
    diff -u calibration_results.json actual.json

No transports, clock adjustments, or on-device permissions are exercised. The acquisition premises are explicit and not calibrated here.
