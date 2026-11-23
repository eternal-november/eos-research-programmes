module
public import ContextualComposition.RelativeTensorTranspose
public import ContextualComposition.RelativeTensorGeneratorComparison
public import Mathlib.CategoryTheory.Functor.Currying

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
universe vB uB vC uC vX uX vM uM vY uY
variable {B : Type uB} {C : Type uC} [Category.{vB} B] [Category.{vC} C]
variable (X : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX}) (M : LocallyDiscrete C ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM}))
variable (Y : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vY,uY})
set_option backward.isDefEq.respectTransparency false

/-- One weak action of C on weak contravariant B-actions supplies both iterated carriers and their mixed interchange. -/
abbrev leftInner := M.comp (Second.action X)
abbrev rightInner := (Middle.transpose M).comp (First.action Y)
abbrev Left := Tensor (leftInner X M) Y
abbrev Right := Tensor X (rightInner M Y)
abbrev row (b : B) := Middle.atIndex M ⟨op b⟩
abbrev column (c : C) := M.obj ⟨c⟩

def leftTriple (b : B) (c : C) :
    ((X.obj ⟨b⟩ × (column M c).obj ⟨op b⟩) × Y.obj ⟨op c⟩) ⥤ Left X M Y :=
  ((insertion X (column M c) b).prod (𝟭 _)) ⋙ insertion (leftInner X M) Y c

def rightTriple (b : B) (c : C) :
    (X.obj ⟨b⟩ × ((column M c).obj ⟨op b⟩ × Y.obj ⟨op c⟩)) ⥤ Right X M Y :=
  ((𝟭 _).prod (insertion (row M b) Y c)) ⋙ insertion X (rightInner M Y) b

theorem right_native {a b : B} (u : a ⟶ b) {c : C} {m m' : (column M c).obj ⟨op b⟩} {y y' : Y.obj ⟨op c⟩}
    (f : m ⟶ m') (g : y ⟶ y') :
    (backward (rightInner M Y) u).map ((insertion (row M b) Y c).map (productMap f g)) =
      (insertion (row M a) Y c).map (productMap ((backward (column M c) u).map f) g) :=
  First.on_native (Middle.change M u.op.toLoc) f g

theorem left_native {c d : C} (v : c ⟶ d) {b : B} {x x' : X.obj ⟨b⟩} {m m' : (column M c).obj ⟨op b⟩}
    (f : x ⟶ x') (g : m ⟶ m') :
    (forward (leftInner X M) v).map ((insertion X (column M c) b).map (productMap f g)) =
      (insertion X (column M d) b).map (productMap f (((M.map v.toLoc).app ⟨op b⟩).toFunctor.map g)) :=
  Second.on_native (M.map v.toLoc) f g

theorem right_unit {b : B} (c : C) (m : (column M c).obj ⟨op b⟩) (y : Y.obj ⟨op c⟩) :
    ((rightInner M Y).mapId ⟨op b⟩).hom.toNatTrans.app ((insertion (row M b) Y c).obj (m,y)) =
      (insertion (row M b) Y c).map (productMap (((column M c).mapId ⟨op b⟩).hom.toNatTrans.app m) (𝟙 y)) := by
  let s := (insertion (row M b) Y c).obj (m,y)
  change (First.mapCell ((Middle.transpose M).mapId ⟨op b⟩).hom.as).app s ≫ (First.identityIso Y (row M b)).hom.toNatTrans.app s = _
  rw [First.identity_hom_app]
  erw [Category.comp_id]
  rfl

theorem right_comp {a b d : B} (u : a ⟶ b) (v : b ⟶ d) (c : C) (m : (column M c).obj ⟨op d⟩) (y : Y.obj ⟨op c⟩) :
    ((rightInner M Y).mapComp v.op.toLoc u.op.toLoc).hom.toNatTrans.app ((insertion (row M d) Y c).obj (m,y)) =
      (insertion (row M a) Y c).map (productMap (((column M c).mapComp v.op.toLoc u.op.toLoc).hom.toNatTrans.app m) (𝟙 y)) := by
  let s := (insertion (row M d) Y c).obj (m,y)
  change (First.mapCell ((Middle.transpose M).mapComp v.op.toLoc u.op.toLoc).hom.as).app s ≫
    (First.compositeIso Y (Middle.change M v.op.toLoc) (Middle.change M u.op.toLoc)).hom.toNatTrans.app s = _
  rw [First.composite_hom_app]
  erw [Category.comp_id]
  rfl

end ContextualComposition.RelativeTensor.Iterated
