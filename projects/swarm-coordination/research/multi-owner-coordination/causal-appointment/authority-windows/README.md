# SC-AUTHORITY-WINDOW-COMPOSITION: When can a cached grant proof admit a new joint operation?

An old report authorizes work before a withdrawal. A later appointment can issue the next grant, but the two powers cannot serve the same handoff if the appointment already observed the withdrawal. Each grant alone has a valid historical cut. This test assumes the port's charter requires one common historical witness; it does not invalidate independently vested grants that are permitted to compose across epochs.

For one contiguous interval per ledger in each grant, keep just the least and greatest causal cuts allowed by each grant. An already checked group accepts a new grant exactly when the bounds overlap after composition. Every infeasible group has a witness involving at most two grants. Allow a single hole from revocation and re-grant, and every proper subfamily can pass while the whole group fails, at arbitrary group sizes.

```sh
set -o pipefail
python3 replay.py | cmp expected.json -
```

[Proof and comparison](Authority_Window_Composition.tex). The finite replay compares the endpoint rule with every causal cut on 20,480 instances and checks the revocation construction up to 256 grants. The discrete fixture separates historical feasibility, current authority and clearance. No distributed implementation, physical actuator test, confidentiality guarantee, held-out mission, or R5 acceptance is claimed.
