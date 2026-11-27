# Stationary dwell can split feasible read times

[Proof and scope](Stationary_Dwell.tex). In the same acceleration-limited
model, a truthful notice may complete only after continuous rest for a
prescribed duration anywhere safe. The longest dwell is about 0.435484.
For a 0.42 dwell, completing at 0.425 or 0.548 works; completing at
0.470 does not. A repeatable controller cannot assume that a known
feasible read time remains feasible if the observation arrives earlier.

Run `node replay.mjs | cmp expected.json -`. Exact rational arithmetic
cross-checks the inequality against integration of the velocity envelope;
it does not execute hardware or measure sensor response. The replay ran
in V8. This is a scoped model, not independent contract acceptance.

[Stationary capture and delayed receipt](capture-receipt/README.md) charge
site travel and dwell separately from waiting for the bit, with sharp
site-dependent cutoff cases.
