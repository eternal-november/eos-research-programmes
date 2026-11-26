# A deadline from three competing formation requirements

Three single-file robots must preserve clearance and two geometric links while serving the requirement named in a report. Any pair of possible requirements admits a shared standby that needs no movement. With all three possible, the exact post-report duration is 7/6 time units. The certificate is a single constraint cycle that uses all three terminal requirements.

The [proof](Formation_Report_Deadline.tex) applies to arbitrary finite families of difference-constrained formations with a common speed-to-acceleration ratio. It converts the continuous control problem into an exact finite feasibility test and constructs a continuous path that obeys the persistent constraints. It does not default to pair checks or assume the robots were stationary at the report. Independently feasible actuators with different ratios need not compose, as the fixed-gap counterexample shows.

The direct endpoint LP ties. The relevant [control barrier function comparison](https://arxiv.org/abs/2210.01354) secures simultaneous input feasibility for a viability domain; a safety controller alone does not return this jointly information-limited minimum deadline. No controller simulation or ranking is claimed. This extends the [single-relay proof](../README.md) to coupled scalar motion and builds on the earlier [speed-only joint corridor check](../../../../corridor-joint-coverage/README.md).

Run with Python 3 and SciPy for the independent LP checks:

    python3 replay.py > actual.json
    diff -u results.json actual.json

The exact certificates are rational. The LP cross-check is numerical. The layout, requirements and timing are authored development inputs, not a field or held-out test.

The [heterogeneous-actuator follow-up](heterogeneous-gap-slack/README.md) gives an exact two-robot bound at arbitrary allowed gap slack for crossed speed and acceleration limits.

The [boundary recheck](boundary-recheck/README.md) determines the exact retained constraint summary for replaceable declarations at fixed terminals, and tests whole batches.

The [braking margin comparison](capped-braking-barriers/README.md) separates relative speed from capped braking power and exact pairwise feasibility from joint input feasibility.
