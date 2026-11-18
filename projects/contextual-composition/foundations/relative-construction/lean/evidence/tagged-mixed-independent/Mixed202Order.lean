import ContextualComposition.TaggedMixed
open CategoryTheory ContextualComposition.GrothendieckStep TaggedMixed
namespace Order202
inductive Pt | star
instance : Category Pt where
  Hom _ _ := Bool → Bool
  id _ := id
  comp f g := g ∘ f
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl
def K : Pt ⥤ Pt where
  obj _ := Pt.star
  map _ := id
  map_id _ := rfl
  map_comp _ _ := rfl
def G : FinalCube.Mix.Grid where
  A := Pt; D := Pt; A' := Pt; D' := Pt
  b := 𝟭 Pt; b' := 𝟭 Pt; p := 𝟭 Pt; q := 𝟭 Pt
  cell := 𝟙 _
def face (u : Bool → Bool) : 𝟭 Pt ⋙ K ⟶ K ⋙ 𝟭 Pt where
  app _ := u
  naturality _ _ _ := rfl
def C : Cube.Map G G where
  f := K; g := K; f' := K; g' := K
  s := face (fun _ => false); t := face Bool.not
  l := face Bool.not; r := face (fun _ => false)
example : Cube.Law C := fun _ => rfl
-- The same two arrows on the right do not commute: reversing their order
-- produces the opposite Boolean at an input. A scalar-addition fixture cannot see this.
example : C.t.app Pt.star ≫ C.r.app Pt.star ≠ C.r.app Pt.star ≫ C.t.app Pt.star := by
  intro h; exact Bool.noConfusion (congrArg (fun k : Pt.star ⟶ Pt.star => k true) h)
end Order202
