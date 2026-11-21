import checks.AugmentedMatrixFubini
open Issue92Probes
-- Deliberate failure: a zero-augmented raw witness is not an empty carrier.
example : zeroWitness.Pos → noWitness.Pos := by
  intro x
  exact x
