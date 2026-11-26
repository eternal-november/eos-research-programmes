# Timely retirement with a mandatory old prefix

[Exact window and proof](Fence_Timing_And_Prefix_Duty.tex).
A prospective withdrawal must both preserve already promised useful
work and prevent all old effects after the cutoff. In the declared
case a remote request is too variable, while a properly timed local
amendment succeeds only for one send tick.

```sh
python3 -B retire.py | cmp results.json -
```

`RetirementSpan.lean` checked on AXLE `lean-4.35.0` with Mathlib
and no `sorryAx`. Actuator and authority bounds are model premises;
the previous source replay does not establish them.
