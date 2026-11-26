# Named withdrawal while an older effect is still live

The earlier placement-generation proof does not cover an operation
that already moved X to a buffer but has not committed. Two old
scopes give the same real prefix and current Y identity. They
differ on whether Y can be independently withdrawn now. See
[claim, native effects, timing and limits](In_Flight_Withdrawal.tex).

Use the named-withdrawal fixture at commit
`e6cfead43ceb1c15d88653c442eb7f762cf09dd4` and its pinned
warehouse inputs. Python 3 plus NumPy:

    python3 -B native.py /path/to/upstream /path/to/named-withdrawal | cmp expected.json -

Pass `--full` to emit every checked row instead of the exact
summary and its canonical-row hash. `LiveScope.lean` was checked
on AXLE Lean 4.35.0. The native fixture uses authored qualified
scope and receipts; no independent case or advantage over an
equally informed exact controller is claimed.

[Ordered native source producer](source-producer/README.md) derives live scope from a complete accepted command suffix. Conflicting amendments have different outcomes before and after acquisition, disjoint ones proceed, and actual unload alone is not carrier clearance. Matched exact gate lookup ties.
