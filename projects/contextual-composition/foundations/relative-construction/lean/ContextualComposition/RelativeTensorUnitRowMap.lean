module
public import ContextualComposition.RelativeTensorUnitRows
public import ContextualComposition.RelativeTensorFactorCells

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
universe v u vY uY
variable {B : Type u} [Category.{v} B]

/-- Identify the hom row with its co-Yoneda presentation by the identity functor on every label category. -/
def unitRowMap (a : B) : row (unitModule B) a ⟶ LeftUnit.represented a where
  app _ := 𝟙 _
  naturality _ := Iso.refl _
  naturality_naturality η := by apply Cat.Hom₂.ext; apply NatTrans.ext; funext p; apply Discrete.hom_eq
  naturality_id i := by apply Cat.Hom₂.ext; apply NatTrans.ext; funext p; apply Discrete.hom_eq
  naturality_comp f g := by apply Cat.Hom₂.ext; apply NatTrans.ext; funext p; apply Discrete.hom_eq

/-- For a diagram with thin fibres, equal component functors force equal strong transformations. -/
private theorem strong_ext_thin {A : Type*} [Bicategory A] {F G : A ⥤ᵖ Cat.{vY,uY}}
    (thin : ∀ i (x y : G.obj i) (f g : x ⟶ y), f = g) (s t : F ⟶ G) (ha : s.app = t.app) : s = t := by
  cases s with
  | mk a n =>
    cases t with
    | mk b m =>
      dsimp at ha
      cases ha
      have h : @n = @m := by
        funext i j f
        apply Iso.ext; apply Cat.Hom₂.ext; apply NatTrans.ext; funext x; apply thin
      cases h
      rfl

/-- The row identification intertwines actual base change with every strong presentation of precomposition that agrees on labels. -/
theorem unitRowMap_change {a b : B} (u : a ⟶ b) (s : LeftUnit.represented b ⟶ LeftUnit.represented a)
    (labels : ∀ (j : B) (p : Discrete (b ⟶ j)), (s.app ⟨j⟩).toFunctor.obj p = Discrete.mk (u ≫ p.as)) :
    Middle.change (unitModule B) u.op.toLoc ≫ unitRowMap a = unitRowMap b ≫ s := by
  apply strong_ext_thin (fun _ _ _ _ _ => Discrete.hom_eq)
  funext j
  apply Cat.Hom.ext
  exact Functor.ext (fun p => (labels j.as p).symm) (fun _ _ _ => Discrete.hom_eq)

variable (Y : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vY,uY})

/-- Reindexing the weak tensor along its curried hom row commutes with identifying the co-Yoneda presentation. -/
theorem unitRowMap_tensor_change {a b : B} (u : a ⟶ b) (s : LeftUnit.represented b ⟶ LeftUnit.represented a)
    (labels : ∀ (j : B) (p : Discrete (b ⟶ j)), (s.app ⟨j⟩).toFunctor.obj p = Discrete.mk (u ≫ p.as)) :
    backward (rightInner (unitModule B) Y) u ⋙ mapFirst (G := Y) (unitRowMap a) =
      mapFirst (G := Y) (unitRowMap b) ⋙ mapFirst (G := Y) s := by
  exact (First.map_composite (G := Y) (Middle.change (unitModule B) u.op.toLoc) (unitRowMap a)).symm.trans
    ((congrArg (fun k => mapFirst (G := Y) k) (unitRowMap_change u s labels)).trans (First.map_composite (G := Y) (unitRowMap b) s))

end ContextualComposition.RelativeTensor.Iterated
