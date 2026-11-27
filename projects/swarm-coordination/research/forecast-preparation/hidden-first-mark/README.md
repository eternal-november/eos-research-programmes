# Forecasting which class needs a reserve after a queue change

Two controlled source laws agree on all allowed old queue observations
and on unconditional tape statistics. They disagree on which early task
class needs a backup after reversing the queue. An earlier experiment
can distinguish them, but uses a reserved slot; a qualified record of
where the diagnostic was rejected changes the exact experiment policy.

[Source boundary, proof and exact stopping rule](Hidden_First_Mark.tex).
The finite source tests use controlled marks, not measured RF or
libc PRNG statistics. Install the exact inputs in [SOURCE.tsv](SOURCE.tsv)
at their listed relative paths, then:

    sh replay.sh /path/to/inputs | cmp expected.json -

Needs Git, Python 3 and C++17. `HiddenVisit.lean` (Lean 4.35 with
Mathlib) checks arithmetic kernels without `sorryAx`.
