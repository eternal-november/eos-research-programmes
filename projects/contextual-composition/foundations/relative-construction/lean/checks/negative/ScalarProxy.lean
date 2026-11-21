import checks.AugmentedMatrixFubini
open Issue92Probes
-- Deliberate failure: equal augmentation and equal early outer data do not
-- imply equal entries of these native coefficient blocks.
example :
    route₁.native firstOut outRow ⟨⟨taggedInput false, rfl⟩, inColumn false⟩ =
    route₂.native firstOut outRow ⟨⟨taggedInput true, rfl⟩, inColumn true⟩ := by
  rw [shear_separates_native_columns.1, shear_separates_native_columns.2]
