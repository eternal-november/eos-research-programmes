module
public import ContextualComposition.TelescopeAmbientActionLaws

@[expose] public section
namespace ContextualComposition.GrothendieckStep.TelescopeAmbientLaws
open CategoryTheory CategoryTheory.Functor Opposite
open FibreValue NativeCleavage CoproductSpan CoproductSpan.All ContextadAmbientPayload AmbientBicategory
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B}
variable (S : P.Split) (A : B) {X Y Z : Obj.{u,v} B}

set_option backward.isDefEq.respectTransparency true

noncomputable abbrev taggedEvaluation (X : Obj.{u,v} B) :=
  ZeroPower.Sum.map (fun n => (component S (underlying X) A n).functor)

private theorem forwardUnit (X : Obj.{u,v} B) : Paste.UnitLaw
    (X := leaves S A (𝟙 X)) (Y := whole S A (𝟙 X)) (F := (PayloadLaws.All.presentation S A (underlying X)).functor)
    (forward S A (𝟙 X)).symm (eqToHom (leafId S A X)) (eqToHom (wholeId S A X)) := by
  apply PayloadLaws.unit (U := leaves S A (𝟙 X)) (V := whole S A (𝟙 X)) (F := (PayloadLaws.All.presentation S A (underlying X)).functor)
    (forward S A (𝟙 X)).symm (leafId S A X) (wholeId S A X) (forwardTransport S A (𝟙 X))

private theorem forwardComp (f : X ⟶ Y) (g : Y ⟶ Z) :
    Paste.CompLaw (X := leaves S A g) (Y := leaves S A f) (W := leaves S A (f ≫ g))
      (X' := whole S A g) (Y' := whole S A f) (W' := whole S A (f ≫ g))
      (F := (PayloadLaws.All.presentation S A (underlying Z)).functor)
      (G := (PayloadLaws.All.presentation S A (underlying Y)).functor)
      (H := (PayloadLaws.All.presentation S A (underlying X)).functor)
      (forward S A (f ≫ g)).symm (forward S A g).symm (forward S A f).symm
      (eqToHom (leafComp S A f g)) (eqToHom (wholeComp S A f g)) :=
  PayloadLaws.comp (U := leaves S A g) (V := leaves S A f) (W := leaves S A (f ≫ g))
    (U' := whole S A g) (V' := whole S A f) (W' := whole S A (f ≫ g)) (F := (PayloadLaws.All.presentation S A (underlying Z)).functor) (G := (PayloadLaws.All.presentation S A (underlying Y)).functor) (H := (PayloadLaws.All.presentation S A (underlying X)).functor)
    (forward S A (f ≫ g)).symm (forward S A g).symm (forward S A f).symm
    (leafComp S A f g) (wholeComp S A f g) (forwardTransport S A (f ≫ g)) (forwardTransport S A g) (forwardTransport S A f)

noncomputable abbrev inverse (f : X ⟶ Y) :
    (PayloadLaws.All.presentation S A (underlying X)).inverse ⋙ leaves S A f ≅
      whole S A f ⋙ (PayloadLaws.All.presentation S A (underlying Y)).inverse :=
  TelescopeGradeChange.inverse_payload (Y := underlying X) (Z := underlying Y) f.hom S A

theorem inverseUnit (X : Obj.{u,v} B) :
    Paste.UnitLaw (X := whole S A (𝟙 X)) (Y := leaves S A (𝟙 X)) (F := (PayloadLaws.All.presentation S A (underlying X)).inverse) (inverse S A (𝟙 X)).symm (eqToHom (wholeId S A X)) (eqToHom (leafId S A X)) :=
  MateLaws.unit (PayloadLaws.All.presentation S A (underlying X)) (s := leaves S A (𝟙 X)) (t := whole S A (𝟙 X)) (forward S A (𝟙 X)) (eqToHom (leafId S A X)) (eqToHom (wholeId S A X)) (forwardUnit S A X)

theorem inverseComp (f : X ⟶ Y) (g : Y ⟶ Z) :
    Paste.CompLaw (X := whole S A g) (Y := whole S A f) (W := whole S A (f ≫ g))
      (X' := leaves S A g) (Y' := leaves S A f) (W' := leaves S A (f ≫ g))
      (F := (PayloadLaws.All.presentation S A (underlying Z)).inverse)
      (G := (PayloadLaws.All.presentation S A (underlying Y)).inverse)
      (H := (PayloadLaws.All.presentation S A (underlying X)).inverse)
      (inverse S A (f ≫ g)).symm
      (inverse S A g).symm (inverse S A f).symm
      (eqToHom (wholeComp S A f g)) (eqToHom (leafComp S A f g)) :=
  MateLaws.comp (PayloadLaws.All.presentation S A (underlying Z)) (PayloadLaws.All.presentation S A (underlying Y))
    (PayloadLaws.All.presentation S A (underlying X)) (X := leaves S A g) (Y := leaves S A f) (W := leaves S A (f ≫ g))
    (X' := whole S A g) (Y' := whole S A f) (W' := whole S A (f ≫ g)) (forward S A (f ≫ g)) (forward S A g) (forward S A f)
    (eqToHom (leafComp S A f g)) (eqToHom (wholeComp S A f g)) (forwardComp S A f g)

/-- Identity pasting at the fixed base object for the actual strong-payload comparison. -/
theorem evaluationUnit (X : Obj.{u,v} B) : Paste.UnitLaw (X := whole S A (𝟙 X)) (Y := iterates S A (𝟙 X)) (F := (evaluation S (underlying X) A).functor)
    (TelescopeAmbientComponents.evaluation_payload S A (𝟙 X)).symm
    (eqToHom (wholeId S A X)) (eqToHom (iterateId S A X)) :=
  Paste.unitLaw (inverse S A (𝟙 X)).symm (tagged S A (𝟙 X)).symm
    (eqToHom (wholeId S A X)) (eqToHom (leafId S A X)) (eqToHom (iterateId S A X))
    (inverseUnit S A X) (PayloadLaws.unit (tagged S A (𝟙 X)).symm (leafId S A X) (iterateId S A X) (taggedTransport S A (𝟙 X)))

end ContextualComposition.GrothendieckStep.TelescopeAmbientLaws
