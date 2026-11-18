import ContextualComposition.ForwardMixed
open CategoryTheory ContextualComposition.GrothendieckStep ForwardMixed
namespace TransportBoundary
inductive Pt | star
instance : Category Pt where
  Hom _ _ := Bool
  id _ := false
  comp f g := Bool.xor f g
  id_comp := by rintro _ _ (_ | _) <;> rfl
  comp_id := by rintro _ _ (_ | _) <;> rfl
  assoc := by rintro _ _ _ _ (_ | _) (_ | _) (_ | _) <;> rfl
def twist : Pt.star ≅ Pt.star where
  hom := true; inv := true; hom_inv_id := rfl; inv_hom_id := rfl
example : ¬ IsTransport twist.hom := by
  rintro ⟨h,e⟩
  change true = false at e
  contradiction
example : TelescopeSquares.Aligned (𝟙 Pt.star) (𝟙 Pt.star) := TelescopeSquares.Aligned.refl _
-- Equal middle arrows do not imply the six-face equation for arbitrary invertible edges.
example : ((𝟙 Pt.star ≫ twist.hom) ≫ 𝟙 Pt.star) ≠ (𝟙 Pt.star ≫ 𝟙 Pt.star ≫ 𝟙 Pt.star) := by
  change true ≠ false; decide
end TransportBoundary
