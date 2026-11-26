Lean 4.35.0 with Mathlib compiled ParityArithmetic.lean without errors or warnings.
The first two audits use only propext and Quot.sound. The rational example also
uses Classical.choice. These check the lattice rounding and numerical
comparison, not the decision-tree reduction or empirical source behavior.
