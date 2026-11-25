# Live amendment of custody timing

[Proof and model](Live_Custody_Timing_Amendment.tex) · [Checked prefix law](DeadlineProfile.lean)

```sh
set -o pipefail
python3 -B deadline_profile.py | cmp deadline_profile.txt -
python3 -B paired_deadline.py | cmp paired-deadline.txt -
lean DeadlineProfile.lean
```

The Python programs share neither an event checker nor a solver between the analytic profile and the absolute-time two-history discriminator. Lean 4.35.0 with Mathlib checks the profile arithmetic, not the port's telemetry. No independent transfer is claimed.
