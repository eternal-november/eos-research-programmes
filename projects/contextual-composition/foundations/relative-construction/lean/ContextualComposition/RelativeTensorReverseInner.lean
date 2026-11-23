module
public import ContextualComposition.RelativeTensorAssociate

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated.Reverse
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
universe vB uB vC uC vX uX vM uM vY uY
variable {B : Type uB} {C : Type uC} [Category.{vB} B] [Category.{vC} C]
variable (X : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX}) (M : LocallyDiscrete C ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM}))
variable (Y : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vY,uY})
set_option backward.isDefEq.respectTransparency false

abbrev insertL (c : C) := insertion (leftInner X M) Y c
abbrev insertM (b : B) (c : C) := insertion X (column M c) b
abbrev atFirst {b : B} (x : X.obj ⟨b⟩) (c : C) := CategoryTheory.Prod.sectR x _ ⋙ insertM X M b c
abbrev nested {b : B} (x : X.obj ⟨b⟩) (c : C) := ((atFirst X M x c).prod (𝟭 _)) ⋙ insertL X M Y c

def innerCocone {b : B} (x : X.obj ⟨b⟩) : Cocone (row M b) Y (Left X M Y) where
  fiber := nested X M Y x
  bal v m y := balancing (leftInner X M) Y v ((insertM X M b _).obj (x,m)) y
  natural := by
    intro c d v m m' y y' f g
    have h := (restrict (𝟭 (Left X M Y))).natural v ((insertM X M b c).map (productMap (𝟙 x) f)) g
    change _ = _ ≫ (insertL X M Y d).map (productMap ((forward (leftInner X M) v).map _) g) at h
    rw [left_native] at h
    exact h
  unit {c} m y := by
    have h := (restrict (𝟭 (Left X M Y))).unit ((insertM X M b c).obj (x,m)) y
    change _ = (insertL X M Y c).map (productMap (((leftInner X M).mapId ⟨c⟩).inv.toNatTrans.app _) _) at h
    erw [left_unit_inverse X M c x m] at h
    exact h
  comp {c d e} v w m y := by
    have h := (restrict (𝟭 (Left X M Y))).comp v w ((insertM X M b c).obj (x,m)) y
    change _ = _ ≫ _ ≫ _ ≫ (insertL X M Y e).map (productMap (((leftInner X M).mapComp v.toLoc w.toLoc).inv.toNatTrans.app _) _) at h
    erw [left_comp_inverse X M v w x m] at h
    change _ = (insertL X M Y c).map (productMap ((atFirst X M x c).map (𝟙 m)) _) ≫ _ ≫ _ ≫ _
    rw [Functor.map_id]
    exact h

def innerMap {b : B} {x x' : X.obj ⟨b⟩} (p : x ⟶ x') : Transformation (innerCocone X M Y x) (innerCocone X M Y x') where
  components c := {
    app := fun z => (insertL X M Y c).map (productMap ((insertM X M b c).map (productMap p (𝟙 z.1))) (𝟙 z.2))
    naturality := by
      intro z z' f
      change (insertL X M Y c).map _ ≫ _ = _ ≫ (insertL X M Y c).map _
      erw [← (insertL X M Y c).map_comp,← (insertL X M Y c).map_comp]
      apply congrArg (insertL X M Y c).map
      apply Prod.ext
      · change (insertM X M b c).map _ ≫ _ = _ ≫ (insertM X M b c).map _
        erw [← (insertM X M b c).map_comp,← (insertM X M b c).map_comp]
        apply congrArg (insertM X M b c).map
        exact Prod.ext ((Category.id_comp _).trans (Category.comp_id _).symm) ((Category.comp_id _).trans (Category.id_comp _).symm)
      · exact (Category.comp_id _).trans (Category.id_comp _).symm }
  square {c d} v m y := by
    have h := (restrict (𝟭 (Left X M Y))).natural v ((insertM X M b c).map (productMap p (𝟙 m))) (𝟙 y)
    change (insertL X M Y c).map (productMap _ ((backward Y v).map (𝟙 y))) ≫ _ =
      _ ≫ (insertL X M Y d).map (productMap ((forward (leftInner X M) v).map _) _) at h
    erw [left_native,Functor.map_id,Functor.map_id] at h
    exact h.symm

def innerFamily (b : B) : X.obj ⟨b⟩ ⥤ Cocone (row M b) Y (Left X M Y) where
  obj := innerCocone X M Y
  map := innerMap X M Y
  map_id x := by
    apply Transformation.ext; funext c; apply NatTrans.ext; funext z
    change (insertL X M Y c).map (productMap ((insertM X M b c).map (𝟙 _)) (𝟙 _)) = 𝟙 _
    rw [Functor.map_id]; exact Functor.map_id _ _
  map_comp f g := by
    apply Transformation.ext; funext c; apply NatTrans.ext; funext z
    change (insertL X M Y c).map (productMap ((insertM X M b c).map (productMap (f ≫ g) (𝟙 z.1))) (𝟙 _)) = _ ≫ _
    erw [← (insertL X M Y c).map_comp]
    apply congrArg (insertL X M Y c).map
    apply Prod.ext
    · change _ = (insertM X M b c).map _ ≫ (insertM X M b c).map _
      rw [← Functor.map_comp]
      exact congrArg (insertM X M b c).map (Prod.ext rfl (Category.id_comp _).symm)
    · exact (Category.id_comp _).symm

def outerFiber (b : B) : (X.obj ⟨b⟩ × (rightInner M Y).obj ⟨op b⟩) ⥤ Left X M Y :=
  Functor.uncurry.obj (innerFamily X M Y b ⋙ extendFunctor)

theorem inner_native {b : B} {c : C} (x : X.obj ⟨b⟩) {m m' : (column M c).obj ⟨op b⟩} {y y' : Y.obj ⟨op c⟩}
    (f : m ⟶ m') (g : y ⟶ y') :
    (innerCocone X M Y x).extend.map ((insertion (row M b) Y c).map (productMap f g)) =
      (insertL X M Y c).map (productMap ((insertM X M b c).map (productMap (𝟙 x) f)) g) :=
  (innerCocone X M Y x).extend_generator (Edge.native (F := row M b) (G := Y) f g)

theorem inner_balance {b : B} {c d : C} (v : c ⟶ d) (x : X.obj ⟨b⟩) (m : (column M c).obj ⟨op b⟩) (y : Y.obj ⟨op d⟩) :
    (innerCocone X M Y x).extend.map (balancing (row M b) Y v m y).hom =
      (balancing (leftInner X M) Y v ((insertM X M b c).obj (x,m)) y).hom :=
  (innerCocone X M Y x).extend_generator (Edge.balance (F := row M b) (G := Y) v m y)

end ContextualComposition.RelativeTensor.Iterated.Reverse
