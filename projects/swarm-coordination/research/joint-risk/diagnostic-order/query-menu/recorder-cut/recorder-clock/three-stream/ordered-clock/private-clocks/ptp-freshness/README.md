# The ingress time can advance without a fresh offset estimate

The [source note](Offset_Age_And_Ingress.tex) and replay check the pinned LinuxPTP synchronization prefix, timestamp processor, and management-report copy. If a sync arrives before the filtered delay is valid, the ingress field changes and the offset can remain from an earlier estimate. A different fixture computes the same offset at the new ingress, giving the same selected report. This checks compiled C with inert time variables, not real clocks, a network, or a running PTP daemon.

Save the pinned [clock.c](https://github.com/richardcochran/linuxptp/blob/227bbd4715bf4cb735be4947e987032f41457585/clock.c) and [tsproc.c](https://github.com/richardcochran/linuxptp/blob/227bbd4715bf4cb735be4947e987032f41457585/tsproc.c). Then run:

    python3 replay.py clock.c tsproc.c > actual.txt
    diff -u results.txt actual.txt

No runtime permissions or network connection are used. The test does not claim that current status necessarily reports this path in a given deployed synchronization configuration.
