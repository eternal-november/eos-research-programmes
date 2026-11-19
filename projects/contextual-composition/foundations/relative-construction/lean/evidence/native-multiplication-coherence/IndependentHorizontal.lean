import Mathlib.CategoryTheory.Category.Basic
/- Finite source-level obstruction. This is a one-object graded monoidal diagram,
   not a formal identification with the implementation's four whisker charts. -/
namespace IndependentHorizontal
open CategoryTheory
inductive Point | star
instance : Category Point where
  Hom _ _ := Bool
  id _ := false
  comp f g := f.xor g
  id_comp := by intro _ _ f; cases f <;> rfl
  comp_id := by intro _ _ f; cases f <;> rfl
  assoc := by intro _ _ _ _ f g h; cases f <;> cases g <;> cases h <;> rfl
/-- Tensor's map on a pair of arrows, same operation as composition. -/
def tens (a b : Bool) := a.xor b
theorem interchange (a b c d : Bool) :
  tens (a.xor b) (c.xor d) = (tens a c).xor (tens b d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl
theorem strictL (a : Bool) : tens false a = a := by cases a <;> rfl
theorem strictR (a : Bool) : tens a false = a := by cases a <;> rfl
theorem strictA (a b c : Bool) : tens (tens a b) c = tens a (tens b c) := by
  cases a <;> cases b <;> cases c <;> rfl
/-- Component k is both natural with respect to every arrow and invertible. -/
theorem component (k f : Bool) : f.xor k = k.xor f ∧ k.xor k = false := by
  cases f <;> cases k <;> decide
def triangle (l r a : Bool) : Prop :=
  a.xor (tens false l) = tens r false
def pentagon (a : Bool) : Prop :=
  a.xor a = ((tens a false).xor a).xor (tens false a)
theorem pentagonNotTriangle : pentagon false ∧ ¬ triangle true false false := by unfold pentagon triangle tens; decide
theorem triangleNotPentagon : triangle false true true ∧ ¬ pentagon true := by unfold pentagon triangle tens; decide
end IndependentHorizontal
