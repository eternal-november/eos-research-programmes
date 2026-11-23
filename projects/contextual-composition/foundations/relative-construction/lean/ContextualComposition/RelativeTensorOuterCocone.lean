module
public import ContextualComposition.RelativeTensorOuterBalance

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
universe vB uB vC uC vX uX vM uM vY uY
variable {B : Type uB} {C : Type uC} [Category.{vB} B] [Category.{vC} C]
variable (X : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX}) (M : LocallyDiscrete C ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM}))
variable (Y : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vY,uY})
set_option backward.isDefEq.respectTransparency false

abbrev leafMap {c : C} (z : Tensor X (column M c)) {y y' : Y.obj ⟨op c⟩} (h : y ⟶ y') :=
  (insertR X M Y z.as.mid).map (productMap (𝟙 z.as.first) ((insertM M Y z.as.mid c).map (productMap (𝟙 z.as.second) h)))

theorem outer_pair {c : C} {z z' : Tensor X (column M c)} (p : z ⟶ z') {y y' : Y.obj ⟨op c⟩} (h : y ⟶ y') :
    (outerFiber X M Y c).map (productMap p h) = leafMap X M Y z h ≫ (innerCocone X M Y c y').extend.map p := rfl

theorem leaf_natural {c d : C} (v : c ⟶ d) (z : Tensor X (column M c)) {y y' : Y.obj ⟨op d⟩} (h : y ⟶ y') :
    leafMap X M Y z ((backward Y v).map h) ≫ (outerComponent X M Y v y' z).hom =
      (outerComponent X M Y v y z).hom ≫ leafMap X M Y ((forward (leftInner X M) v).obj z) h := by
  change (insertR X M Y z.as.mid).map _ ≫ (insertR X M Y z.as.mid).map _ =
    (insertR X M Y z.as.mid).map _ ≫ (insertR X M Y z.as.mid).map _
  rw [← Functor.map_comp,← Functor.map_comp]
  apply congrArg (insertR X M Y z.as.mid).map
  apply Prod.ext
  · rfl
  · have q := (restrict (𝟭 (Tensor (row M z.as.mid) Y))).natural v (𝟙 z.as.second) h
    change _ = _ ≫ (insertM M Y z.as.mid d).map (productMap ((forward (row M z.as.mid) v).map (𝟙 z.as.second)) h) at q
    rw [Functor.map_id] at q
    exact q

theorem outer_natural {c d : C} (v : c ⟶ d) {z z' : Tensor X (column M c)} (p : z ⟶ z') {y y' : Y.obj ⟨op d⟩} (h : y ⟶ y') :
    (outerFiber X M Y c).map (productMap p ((backward Y v).map h)) ≫ (outerComponent X M Y v y' z').hom =
    (outerComponent X M Y v y z).hom ≫ (outerFiber X M Y d).map (productMap ((forward (leftInner X M) v).map p) h) := by
  rw [outer_pair,outer_pair,Category.assoc]
  have hz := (outerSquare X M Y v y').hom.naturality p
  change _ ≫ (outerComponent X M Y v y' z').hom = (outerComponent X M Y v y' z).hom ≫ _ at hz
  rw [hz,← Category.assoc,leaf_natural,Category.assoc]
  rfl

theorem left_unit_inverse {b : B} (c : C) (x : X.obj ⟨b⟩) (m : (column M c).obj ⟨op b⟩) :
    ((leftInner X M).mapId ⟨c⟩).inv.toNatTrans.app ((insertion X (column M c) b).obj (x,m)) =
      (insertion X (column M c) b).map (productMap (𝟙 x) (((row M b).mapId ⟨c⟩).inv.toNatTrans.app m)) := by
  let z := (insertion X (column M c) b).obj (x,m)
  change (Second.identityIso X (column M c)).inv.toNatTrans.app z ≫ (Second.mapCell ((M.mapId ⟨c⟩).inv.as)).app z = _
  have u : (Second.identityIso X (column M c)).inv.toNatTrans.app z = 𝟙 _ := by
    change (eqToHom (Second.map_identity (F := X) (G := column M c)).symm).app z = _
    rw [eqToHom_app]; rfl
  erw [u,Category.id_comp,Second.cell_app]
  change _ = (insertion X (column M c) b).map (productMap (𝟙 x) (𝟙 _ ≫ _))
  erw [Category.id_comp]
  rfl

theorem left_comp_inverse {b : B} {c d e : C} (v : c ⟶ d) (w : d ⟶ e) (x : X.obj ⟨b⟩) (m : (column M c).obj ⟨op b⟩) :
    ((leftInner X M).mapComp v.toLoc w.toLoc).inv.toNatTrans.app ((insertion X (column M c) b).obj (x,m)) =
      (insertion X (column M e) b).map (productMap (𝟙 x) (((row M b).mapComp v.toLoc w.toLoc).inv.toNatTrans.app m)) := by
  let z := (insertion X (column M c) b).obj (x,m)
  change (Second.compositeIso X (M.map v.toLoc) (M.map w.toLoc)).inv.toNatTrans.app z ≫ (Second.mapCell ((M.mapComp v.toLoc w.toLoc).inv.as)).app z = _
  erw [Second.composite_inv_app, Category.id_comp, Second.cell_app]
  change _ = (insertion X (column M e) b).map (productMap (𝟙 x) (𝟙 _ ≫ _))
  erw [Category.id_comp]
  rfl

end ContextualComposition.RelativeTensor.Iterated
