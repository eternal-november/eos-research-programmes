import ContextualComposition.MateLaws
open CategoryTheory CategoryTheory.Functor
open ContextualComposition.GrothendieckStep.SumChange

namespace TwistedMateProbe
inductive Point | star
instance : Category Point where
  Hom _ _ := Bool
  id _ := false
  comp f g := Bool.xor f g
  id_comp := by rintro _ _ (_ | _) <;> rfl
  comp_id := by rintro _ _ (_ | _) <;> rfl
  assoc := by rintro _ _ _ _ (_ | _) (_ | _) (_ | _) <;> rfl

def flipIso (x : Point) : x ≅ x where
  hom := true
  inv := true
  hom_inv_id := rfl
  inv_hom_id := rfl

def twist : Point ≌ Point where
  functor := 𝟭 Point
  inverse := 𝟭 Point
  unitIso := NatIso.ofComponents (fun x => flipIso x) (by rintro x y (_|_) <;> rfl)
  counitIso := NatIso.ofComponents (fun x => flipIso x) (by rintro x y (_|_) <;> rfl)
  functor_unitIso_comp := by intro x; rfl

def cell : (CategoryTheory.Equivalence.refl : Point ≌ Point).functor ⋙ 𝟭 Point ≅ 𝟭 Point ⋙ twist.functor := Iso.refl _
def back := inverseSquare (CategoryTheory.Equivalence.refl : Point ≌ Point) twist cell
example : cell.hom.app Point.star = 𝟙 Point.star := rfl
example : back.hom.app Point.star = true := rfl
example : back.hom.app Point.star ≠ 𝟙 Point.star := by change true ≠ false; decide
abbrev ordinary : Point ≌ Point := CategoryTheory.Equivalence.refl
def second : twist.functor ⋙ 𝟭 Point ≅ 𝟭 Point ⋙ ordinary.functor := Iso.refl _
def direct : ordinary.functor ⋙ 𝟭 Point ≅ 𝟭 Point ⋙ ordinary.functor := Iso.refl _
example : (inverseSquare twist ordinary second).hom.app Point.star = true := rfl
example : (inverseSquare ordinary ordinary direct).hom.app Point.star = false := rfl

open ContextualComposition.GrothendieckStep
-- Two genuine correction maps compose to the trivial direct comparison.
example : FibreValue.Paste.CompLaw
    (inverseSquare ordinary ordinary direct).symm
    (inverseSquare twist ordinary second).symm
    (inverseSquare ordinary twist cell).symm
    (𝟙 (𝟭 Point)) (𝟙 (𝟭 Point)) :=
  MateLaws.comp ordinary twist ordinary direct second cell _ _ (fun _ => rfl)
end TwistedMateProbe
