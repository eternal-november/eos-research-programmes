module
public import ContextualComposition.RelativeTensorIterates

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
universe vB uB vC uC vX uX vM uM vY uY
variable {B : Type uB} {C : Type uC} [Category.{vB} B] [Category.{vC} C]
variable (X : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX}) (M : LocallyDiscrete C ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM}))
variable (Y : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vY,uY})
set_option backward.isDefEq.respectTransparency false

def rowPoint (b : B) (c : C) (y : Y.obj ⟨op c⟩) :=
  (CategoryTheory.Prod.sectL _ y) ⋙ insertion (row M b) Y c
def nested (b : B) (c : C) (y : Y.obj ⟨op c⟩) :=
  ((𝟭 _).prod (rowPoint M Y b c y)) ⋙ insertion X (rightInner M Y) b

/-- At a fixed last leaf the right-associated tensor satisfies the full inner balance, including its weak compositor. -/
def innerCocone (c : C) (y : Y.obj ⟨op c⟩) : Cocone X (column M c) (Right X M Y) where
  fiber b := nested X M Y b c y
  bal u x m := balancing X (rightInner M Y) u x ((insertion (row M _) Y c).obj (m,y))
  natural := by
    intro i j u x x' m m' f g
    let S := restrict (𝟭 (Right X M Y))
    have h := S.natural u f ((rowPoint M Y j c y).map g)
    change (insertion X (rightInner M Y) i).map (productMap f ((backward (rightInner M Y) u).map
      ((insertion (row M j) Y c).map (productMap g (𝟙 y))))) ≫ _ = _ at h
    rw [right_native] at h
    exact h
  unit {i} x m := by
    have h := (restrict (𝟭 (Right X M Y))).unit x ((insertion (row M i) Y c).obj (m,y))
    change _ = (insertion X (rightInner M Y) i).map (productMap _ (((rightInner M Y).mapId ⟨op i⟩).hom.toNatTrans.app _)) at h
    erw [right_unit M Y c m y] at h
    exact h
  comp {i j k} u v x m := by
    have h := (restrict (𝟭 (Right X M Y))).comp u v x ((insertion (row M k) Y c).obj (m,y))
    change _ = (insertion X (rightInner M Y) i).map (productMap (𝟙 x)
      (((rightInner M Y).mapComp v.op.toLoc u.op.toLoc).hom.toNatTrans.app _)) ≫ _ ≫ _ ≫ _ at h
    erw [right_comp M Y u v c m y] at h
    change _ = _ ≫ _ ≫ _ ≫ (insertion X (rightInner M Y) k).map (productMap _ ((rowPoint M Y k c y).map (𝟙 m)))
    rw [Functor.map_id]
    exact h

def innerMap {c : C} {y y' : Y.obj ⟨op c⟩} (p : y ⟶ y') :
    Transformation (innerCocone X M Y c y) (innerCocone X M Y c y') where
  components b := {
    app := fun x => (insertion X (rightInner M Y) b).map (productMap (𝟙 x.1)
      ((insertion (row M b) Y c).map (productMap (𝟙 x.2) p)))
    naturality := by
      intro x x' f
      change (insertion X (rightInner M Y) b).map _ ≫ _ = _ ≫ (insertion X (rightInner M Y) b).map _
      erw [← (insertion X (rightInner M Y) b).map_comp,← (insertion X (rightInner M Y) b).map_comp]
      apply congrArg (insertion X (rightInner M Y) b).map
      apply Prod.ext
      · exact (Category.comp_id _).trans (Category.id_comp _).symm
      · change (insertion (row M b) Y c).map _ ≫ _ = _ ≫ (insertion (row M b) Y c).map _
        erw [← (insertion (row M b) Y c).map_comp,← (insertion (row M b) Y c).map_comp]
        apply congrArg (insertion (row M b) Y c).map
        exact Prod.ext ((Category.comp_id _).trans (Category.id_comp _).symm) ((Category.id_comp _).trans (Category.comp_id _).symm) }
  square {i j} u x m := by
    have h := (restrict (𝟭 (Right X M Y))).natural u (𝟙 x) ((insertion (row M j) Y c).map (productMap (𝟙 m) p))
    change (insertion X (rightInner M Y) i).map (productMap (𝟙 x) ((backward (rightInner M Y) u).map _)) ≫ _ =
      _ ≫ (insertion X (rightInner M Y) j).map (productMap ((forward X u).map (𝟙 x)) _) at h
    erw [right_native,Functor.map_id,Functor.map_id] at h
    exact h.symm

def innerFamily (c : C) : Y.obj ⟨op c⟩ ⥤ Cocone X (column M c) (Right X M Y) where
  obj := innerCocone X M Y c
  map := innerMap X M Y
  map_id y := by
    apply Transformation.ext; funext i; apply NatTrans.ext; funext x
    change (insertion X (rightInner M Y) i).map (productMap (𝟙 _) ((insertion (row M i) Y c).map (𝟙 _))) = 𝟙 _
    rw [Functor.map_id]
    exact Functor.map_id _ _
  map_comp f g := by
    apply Transformation.ext; funext i; apply NatTrans.ext; funext x
    change (insertion X (rightInner M Y) i).map (productMap (𝟙 _) ((insertion (row M i) Y c).map (productMap (𝟙 _) (f ≫ g)))) = _ ≫ _
    erw [← (insertion X (rightInner M Y) i).map_comp]
    apply congrArg (insertion X (rightInner M Y) i).map
    apply Prod.ext
    · exact (Category.id_comp _).symm
    · change _ = (insertion (row M i) Y c).map _ ≫ (insertion (row M i) Y c).map _
      rw [← Functor.map_comp]
      exact congrArg (insertion (row M i) Y c).map (Prod.ext (Category.id_comp _).symm rfl)

/-- The inner rebracketing functor on all inner paths and arbitrary last-leaf arrows. -/
def outerFiber (c : C) : ((leftInner X M).obj ⟨c⟩ × Y.obj ⟨op c⟩) ⥤ Right X M Y :=
  CategoryTheory.Prod.swap _ _ ⋙ Functor.uncurry.obj (innerFamily X M Y c ⋙ extendFunctor)

end ContextualComposition.RelativeTensor.Iterated
