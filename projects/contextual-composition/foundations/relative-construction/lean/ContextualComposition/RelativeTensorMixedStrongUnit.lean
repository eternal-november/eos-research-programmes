module
public import ContextualComposition.RelativeTensorMixedUnitJoint

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

universe v u
variable {B : Type u} [Category.{max u v} B]
variable (M N : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{max u v,max u v}))
variable (jM : unitModule B ⟶ M) (jN : unitModule B ⟶ N)
local notation "I" => unitModule B
local notation "H" => middleComposite M N

def mixedUnitColumnOutput {c d : B} (g : c ⟶ d) (a : LocallyDiscrete Bᵒᵖ) :
    (((I).map g.toLoc).app a).toFunctor ⋙ ((mixedUnitInputColumn M N jM jN d).app a).toFunctor ≅
    ((mixedUnitInputColumn M N jM jN c).app a).toFunctor ⋙ (((H).map g.toLoc).app a).toFunctor :=
  mixedUnitOutput M N jM jN (a := a.as.unop) g

set_option maxHeartbeats 500000 in
theorem mixedUnitColumnCube {c d : B} (g : c ⟶ d) :
    ColumnCubeLaw ((I).map g.toLoc) ((H).map g.toLoc)
      (mixedUnitInputColumn M N jM jN c) (mixedUnitInputColumn M N jM jN d)
      (mixedUnitColumnOutput M N jM jN g) := by
  intro a b f
  change MixedUnitJoint M N jM jN f.as.unop g
  exact mixedUnitInputOutput_compatibility M N jM jN f.as.unop g

theorem mixedUnitOuterIdentities :
    OrdinaryRawUnit (mixedUnitInputColumn M N jM jN)
      (fun f => mixedUnitColumnOutput M N jM jN f) := by
  intro d a
  exact mixedUnitOutput_identity M N jM jN a.as.unop d

theorem mixedUnitOuterCompositors :
    OrdinaryRawComp (mixedUnitInputColumn M N jM jN)
      (fun f => mixedUnitColumnOutput M N jM jN f) := by
  intro a b c f g x
  exact mixedUnitOutput_composition M N jM jN x.as.unop f g

/-- The original mixed unit bundled as a strong transformation between the
actual weak curried modules, at shared native Cat levels. -/
def mixedUnit : I ⟶ H :=
  strongCurriedFromOrdinaryRawLaws (F := I) (G := H) (mixedUnitInputColumn M N jM jN)
    (fun f => mixedUnitColumnOutput M N jM jN f)
    (fun {c d} g => @mixedUnitColumnCube.{v,u} B _ M N jM jN c d g)
    (mixedUnitOuterIdentities M N jM jN) (mixedUnitOuterCompositors M N jM jN)

theorem mixedUnit_column (d : B) :
    (mixedUnit M N jM jN).app ⟨d⟩ = mixedUnitInputColumn M N jM jN d := rfl

theorem mixedUnit_app (a d : B) :
    HEq (((mixedUnit M N jM jN).app ⟨d⟩).app ⟨op a⟩).toFunctor
      (mixedUnitAt M N jM jN a d) :=
  mixedUnitInputColumn_app M N jM jN d a

theorem mixedUnit_input {a b : B} (f : a ⟶ b) (d : B) :
    Cat.Hom.toNatIso (((mixedUnit M N jM jN).app ⟨d⟩).naturality f.op.toLoc) =
      mixedUnitInput M N jM jN (b := d) f :=
  mixedUnitInputColumn_naturality M N jM jN d f

theorem mixedUnit_output (a : B) {c d : B} (g : c ⟶ d) :
    Cat.Hom.toNatIso ((Middle.evaluate (⟨op a⟩ : LocallyDiscrete Bᵒᵖ)).map₂Iso
      ((mixedUnit M N jM jN).naturality g.toLoc)) =
      mixedUnitOutput M N jM jN (a := a) g := rfl

end ContextualComposition.RelativeTensor.Iterated
