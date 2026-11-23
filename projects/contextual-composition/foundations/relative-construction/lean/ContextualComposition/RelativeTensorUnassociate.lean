module
public import ContextualComposition.RelativeTensorReverseBalance

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated.Reverse
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
universe vB uB vC uC vX uX vM uM vY uY
variable {B : Type uB} {C : Type uC} [Category.{vB} B] [Category.{vC} C]
variable (X : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX}) (M : LocallyDiscrete C ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM}))
variable (Y : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vY,uY})
set_option backward.isDefEq.respectTransparency false

abbrev leafMap {b : B} (z : Tensor (row M b) Y) {x x' : X.obj ⟨b⟩} (h : x ⟶ x') :=
  (insertL X M Y z.as.mid).map (productMap ((insertM X M b z.as.mid).map (productMap h (𝟙 z.as.first))) (𝟙 z.as.second))
abbrev keep {c : C} (y : Y.obj ⟨op c⟩) := CategoryTheory.Prod.sectL ((leftInner X M).obj ⟨c⟩) y ⋙ insertL X M Y c

theorem outer_pair {b : B} {x x' : X.obj ⟨b⟩} (h : x ⟶ x') {z z' : Tensor (row M b) Y} (p : z ⟶ z') :
    (outerFiber X M Y b).map (productMap h p) = leafMap X M Y z h ≫ (innerCocone X M Y x').extend.map p := rfl

theorem leaf_natural {a b : B} (u : a ⟶ b) (z : Tensor (row M b) Y) {x x' : X.obj ⟨a⟩} (f : x ⟶ x') :
    leafMap X M Y ((backward (rightInner M Y) u).obj z) f ≫ (outerComponent X M Y u x' z).hom =
      (outerComponent X M Y u x z).hom ≫ leafMap X M Y z ((forward X u).map f) := by
  change (insertL X M Y z.as.mid).map _ ≫ (insertL X M Y z.as.mid).map _ =
    (insertL X M Y z.as.mid).map _ ≫ (insertL X M Y z.as.mid).map _
  rw [← Functor.map_comp,← Functor.map_comp]
  apply congrArg (insertL X M Y z.as.mid).map
  apply Prod.ext
  · have h := (restrict (𝟭 (Tensor X (column M z.as.mid)))).natural u f (𝟙 z.as.first)
    change (insertM X M a z.as.mid).map (productMap f ((backward (column M z.as.mid) u).map (𝟙 z.as.first))) ≫ _ = _ at h
    rw [Functor.map_id] at h
    exact h
  · rfl

theorem outer_natural {a b : B} (u : a ⟶ b) {x x' : X.obj ⟨a⟩} (f : x ⟶ x') {z z' : Tensor (row M b) Y} (p : z ⟶ z') :
    (outerFiber X M Y a).map (productMap f ((backward (rightInner M Y) u).map p)) ≫ (outerComponent X M Y u x' z').hom =
      (outerComponent X M Y u x z).hom ≫ (outerFiber X M Y b).map (productMap ((forward X u).map f) p) := by
  rw [outer_pair,outer_pair,Category.assoc]
  have hz := (outerSquare X M Y u x').hom.naturality p
  change _ ≫ (outerComponent X M Y u x' z').hom = (outerComponent X M Y u x' z).hom ≫ _ at hz
  erw [hz,← Category.assoc,leaf_natural,Category.assoc]

theorem outer_step {b : B} {c : C} {x x' : X.obj ⟨b⟩} (f : x ⟶ x') {m m' : (column M c).obj ⟨op b⟩} (g : m ⟶ m') (y : Y.obj ⟨op c⟩) :
    (outerFiber X M Y b).map (productMap f ((insertion (row M b) Y c).map (productMap g (𝟙 y)))) =
    (keep X M Y y).map ((insertM X M b c).map (productMap f g)) := by
  rw [outer_pair,inner_native]
  change (keep X M Y y).map ((insertM X M b c).map (productMap f (𝟙 m))) ≫
    (keep X M Y y).map ((insertM X M b c).map (productMap (𝟙 x') g)) = _
  rw [← (keep X M Y y).map_comp,← (insertM X M b c).map_comp]
  apply congrArg (keep X M Y y).map
  apply congrArg (insertM X M b c).map
  exact Prod.ext (Category.comp_id _) (Category.id_comp _)

theorem outer_leaf {b : B} {c : C} {x x' : X.obj ⟨b⟩} (f : x ⟶ x') (m : (column M c).obj ⟨op b⟩) (y : Y.obj ⟨op c⟩) :
    (outerFiber X M Y b).map (productMap f (𝟙 ((insertion (row M b) Y c).obj (m,y)))) =
      (keep X M Y y).map ((insertM X M b c).map (productMap f (𝟙 m))) := by
  erw [outer_pair,Functor.map_id,Category.comp_id]

theorem outer_unit {b : B} (x : X.obj ⟨b⟩) (z : Tensor (row M b) Y) :
    (outerComponent X M Y (𝟙 b) x z).hom =
      (outerFiber X M Y b).map (productMap ((X.mapId ⟨b⟩).inv.toNatTrans.app x) (((rightInner M Y).mapId ⟨op b⟩).hom.toNatTrans.app z)) := by
  obtain ⟨⟨c,m,y⟩⟩ := z
  let z := (insertion (row M b) Y c).obj (m,y)
  change (keep X M Y y).map (balancing X (column M c) (𝟙 b) x m).hom = (outerFiber X M Y b).map (productMap _ (((rightInner M Y).mapId ⟨op b⟩).hom.toNatTrans.app z))
  rw [right_unit,outer_step]
  exact congrArg (keep X M Y y).map ((restrict (𝟭 (Tensor X (column M c)))).unit x m)

theorem outer_comp {a b d : B} (u : a ⟶ b) (v : b ⟶ d) (x : X.obj ⟨a⟩) (z : Tensor (row M d) Y) :
    (outerComponent X M Y (u ≫ v) x z).hom =
      (outerFiber X M Y a).map (productMap (𝟙 x) (((rightInner M Y).mapComp v.op.toLoc u.op.toLoc).hom.toNatTrans.app z)) ≫
      (outerComponent X M Y u x ((backward (rightInner M Y) v).obj z)).hom ≫
      (outerComponent X M Y v ((forward X u).obj x) z).hom ≫
      (outerFiber X M Y d).map (productMap ((X.mapComp u.toLoc v.toLoc).inv.toNatTrans.app x) (𝟙 z)) := by
  obtain ⟨⟨c,m,y⟩⟩ := z
  let z := (insertion (row M d) Y c).obj (m,y)
  change (keep X M Y y).map (balancing X (column M c) (u ≫ v) x m).hom =
    (outerFiber X M Y a).map (productMap _ (((rightInner M Y).mapComp v.op.toLoc u.op.toLoc).hom.toNatTrans.app z)) ≫
      _ ≫ _ ≫ (outerFiber X M Y d).map (productMap _ (𝟙 z))
  rw [right_comp,outer_step,outer_leaf]
  have h := congrArg (keep X M Y y).map ((restrict (𝟭 (Tensor X (column M c)))).comp u v x m)
  simp only [Functor.map_comp] at h
  exact h

def outerCocone : Cocone X (rightInner M Y) (Left X M Y) where
  fiber := outerFiber X M Y
  bal u x z := outerComponent X M Y u x z
  natural := by intro i j u x x' z z' f g; exact outer_natural X M Y u f g
  unit := outer_unit X M Y
  comp := outer_comp X M Y

def unassociate : Right X M Y ⥤ Left X M Y := (outerCocone X M Y).extend

theorem unassociate_outer_balance {a b : B} (u : a ⟶ b) (x : X.obj ⟨a⟩) (z : Tensor (row M b) Y) :
    (unassociate X M Y).map (balancing X (rightInner M Y) u x z).hom = (outerComponent X M Y u x z).hom :=
  (outerCocone X M Y).extend_generator (Edge.balance (F := X) (G := rightInner M Y) u x z)

end ContextualComposition.RelativeTensor.Iterated.Reverse
