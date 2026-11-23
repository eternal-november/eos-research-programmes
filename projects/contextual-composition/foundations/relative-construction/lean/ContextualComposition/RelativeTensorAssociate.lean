module
public import ContextualComposition.RelativeTensorOuterCocone

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
universe vB uB vC uC vX uX vM uM vY uY
variable {B : Type uB} {C : Type uC} [Category.{vB} B] [Category.{vC} C]
variable (X : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX}) (M : LocallyDiscrete C ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM}))
variable (Y : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vY,uY})
set_option backward.isDefEq.respectTransparency false

abbrev keep {b : B} (x : X.obj ⟨b⟩) := CategoryTheory.Prod.sectR x ((rightInner M Y).obj ⟨op b⟩) ⋙ insertR X M Y b

theorem outer_step {b : B} {c : C} (x : X.obj ⟨b⟩) {m m' : (column M c).obj ⟨op b⟩} (f : m ⟶ m')
    {y y' : Y.obj ⟨op c⟩} (g : y ⟶ y') :
    (outerFiber X M Y c).map (productMap ((insertion X (column M c) b).map (productMap (𝟙 x) f)) g) =
      (keep X M Y x).map ((insertM M Y b c).map (productMap f g)) := by
  rw [outer_pair,inner_native]
  change (keep X M Y x).map ((insertM M Y b c).map (productMap (𝟙 m) g)) ≫
    (keep X M Y x).map ((insertM M Y b c).map (productMap f (𝟙 y'))) = _
  rw [← (keep X M Y x).map_comp,← (insertM M Y b c).map_comp]
  apply congrArg (keep X M Y x).map
  apply congrArg (insertM M Y b c).map
  exact Prod.ext (Category.id_comp _) (Category.comp_id _)

theorem outer_leaf {b : B} {c : C} (x : X.obj ⟨b⟩) (m : (column M c).obj ⟨op b⟩)
    {y y' : Y.obj ⟨op c⟩} (g : y ⟶ y') :
    (outerFiber X M Y c).map (productMap (𝟙 ((insertion X (column M c) b).obj (x,m))) g) =
      (keep X M Y x).map ((insertM M Y b c).map (productMap (𝟙 m) g)) := by
  erw [outer_pair,Functor.map_id,Category.comp_id]

theorem outer_unit {c : C} (z : Tensor X (column M c)) (y : Y.obj ⟨op c⟩) :
    (outerComponent X M Y (𝟙 c) y z).hom =
      (outerFiber X M Y c).map (productMap (((leftInner X M).mapId ⟨c⟩).inv.toNatTrans.app z) ((Y.mapId ⟨op c⟩).hom.toNatTrans.app y)) := by
  obtain ⟨⟨b,x,m⟩⟩ := z
  let z := (insertion X (column M c) b).obj (x,m)
  change (keep X M Y x).map (balancing (row M b) Y (𝟙 c) m y).hom =
    (outerFiber X M Y c).map (productMap (((leftInner X M).mapId ⟨c⟩).inv.toNatTrans.app z) _)
  rw [left_unit_inverse,outer_step]
  exact congrArg (keep X M Y x).map ((restrict (𝟭 (Tensor (row M b) Y))).unit m y)

theorem outer_comp {c d e : C} (v : c ⟶ d) (w : d ⟶ e) (z : Tensor X (column M c)) (y : Y.obj ⟨op e⟩) :
    (outerComponent X M Y (v ≫ w) y z).hom =
      (outerFiber X M Y c).map (productMap (𝟙 z) ((Y.mapComp w.op.toLoc v.op.toLoc).hom.toNatTrans.app y)) ≫
      (outerComponent X M Y v ((backward Y w).obj y) z).hom ≫
      (outerComponent X M Y w y ((forward (leftInner X M) v).obj z)).hom ≫
      (outerFiber X M Y e).map (productMap (((leftInner X M).mapComp v.toLoc w.toLoc).inv.toNatTrans.app z) (𝟙 y)) := by
  obtain ⟨⟨b,x,m⟩⟩ := z
  let z := (insertion X (column M c) b).obj (x,m)
  change (keep X M Y x).map (balancing (row M b) Y (v ≫ w) m y).hom =
    (outerFiber X M Y c).map (productMap (𝟙 z) _) ≫ _ ≫ _ ≫ (outerFiber X M Y e).map
      (productMap (((leftInner X M).mapComp v.toLoc w.toLoc).inv.toNatTrans.app z) _)
  rw [outer_leaf,left_comp_inverse,outer_step]
  have h := congrArg (keep X M Y x).map ((restrict (𝟭 (Tensor (row M b) Y))).comp v w m y)
  simp only [Functor.map_comp] at h
  exact h

/-- A functor on the true iterated quotient, including both weak action compositors and their mixed balance comparison. -/
def associatingCocone : Cocone (leftInner X M) Y (Right X M Y) where
  fiber := outerFiber X M Y
  bal v z y := outerComponent X M Y v y z
  natural := by intro i j u z z' y y' f g; exact outer_natural X M Y u f g
  unit := outer_unit X M Y
  comp := outer_comp X M Y

def associate : Left X M Y ⥤ Right X M Y := (associatingCocone X M Y).extend

theorem associate_outer_balance {c d : C} (v : c ⟶ d) (z : Tensor X (column M c)) (y : Y.obj ⟨op d⟩) :
    (associate X M Y).map (balancing (leftInner X M) Y v z y).hom = (outerComponent X M Y v y z).hom :=
  (associatingCocone X M Y).extend_generator (Edge.balance (F := leftInner X M) (G := Y) v z y)

end ContextualComposition.RelativeTensor.Iterated
