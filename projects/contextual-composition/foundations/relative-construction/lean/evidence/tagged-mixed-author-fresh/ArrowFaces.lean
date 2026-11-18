import ContextualComposition.TaggedMixed
open CategoryTheory CategoryTheory.Functor ContextualComposition.GrothendieckStep
open TaggedMixed
namespace ArrowFaceProbe
inductive Pt | star
instance : Category Pt where
  Hom _ _ := Nat
  id _ := 0
  comp f g := f+g
  id_comp := by intros; apply Nat.zero_add
  comp_id := by intros; apply Nat.add_zero
  assoc := by intros; apply Nat.add_assoc
def cell (k : Nat) : 𝟭 Pt ⋙ 𝟭 Pt ⟶ 𝟭 Pt ⋙ 𝟭 Pt where
  app _ := k
  naturality _ _ f := Nat.add_comm f k
def grid (k : Nat) : FinalCube.Mix.Grid where
  A := Pt; D := Pt; A' := Pt; D' := Pt
  b := 𝟭 _; b' := 𝟭 _; p := 𝟭 _; q := 𝟭 _
  cell := cell k
def cube (l r : Nat) : Cube.Map (grid 15) (grid 8) where
  f := 𝟭 _; g := 𝟭 _; f' := 𝟭 _; g' := 𝟭 _
  s := cell 5; t := cell 3; l := cell l; r := cell r
-- (15+3)+2 = 7+(5+8); replacing either payload face, or both, breaks the equation.
example : Cube.Law (cube 7 2) := by intro x; rfl
example : ¬ Cube.Law (cube 0 2) := by intro h; have e := h Pt.star; change 20 = 13 at e; contradiction
example : ¬ Cube.Law (cube 7 0) := by intro h; have e := h Pt.star; change 18 = 20 at e; contradiction
example : ¬ Cube.Law (cube 0 0) := by intro h; have e := h Pt.star; change 18 = 13 at e; contradiction
#check (Cube.diagram_iff (cube 7 2)).mp (by intro x; rfl)
end ArrowFaceProbe
