# Reading the notice at low speed changes the deadline

[Proof and limits](Speed_Qualified_Notice.tex). The two known inspection
windows and their geometry have not changed. Requiring the truthful
notice to be taken while stopped changes the latest useful acquisition
from about 0.604725 to about 0.548224. The exact cutoff is a piecewise
linear function of the permitted reading speed until it reaches the
unrestricted cutoff. A backward preparation move still lets the
stationary reader cover both outcomes.

Twelve speed caps check lower and upper certificates to within one
millionth of a model time unit, with 1,109 exact quadratic inequality
checks. Run `node replay.mjs | cmp expected.json -` with Node 22 or later.
Checked in exact V8; Lean 4.36.0 plus Mathlib checks the scalar cap algebra.
The read is a stipulated instantaneous qualified observation, not
verification of a real sensor, dwell assumption, or an independent mission.
