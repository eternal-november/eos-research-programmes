# Designation lifetime through the due crossing

The selected load can change after a true report, actual old unload,
and physical clearance by the old carrier. The new demand is still
timely with a different standing footprint. See
[scope and source argument](Designation_Lifetime.tex).

Use pinned commit `01f98f4c46719da4ece3c7c9b648a4bcf740b101` for the
previous `deferred-placement` study and the upstream native sources it
declares. The adapter verifies and modifies only the specified local
replayer's timing parameters, not the frozen receiver or native code:

    python3 -B replay.py /path/to/upstream ../deferred-placement | cmp expected.json -

Requires NumPy. The fixed-site comparison isolates the footprint; it
does not supply the earlier controller with hindsight.
