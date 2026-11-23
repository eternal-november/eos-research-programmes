module
public import ContextualComposition.TelescopeAmbientIdentity

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

/-- The square of the published evaluation, with its two boundary functors explicit. -/
noncomputable def evaluationSquare (f : X ⟶ Y) :
    whole S A f ⋙ (evaluation S (underlying Y) A).functor ≅ (evaluation S (underlying X) A).functor ⋙ iterates S A f :=
  (TelescopeAmbientComponents.evaluation_payload S A f).symm

noncomputable def pasted (f : X ⟶ Y) :
    whole S A f ⋙ (evaluation S (underlying Y) A).functor ≅ (evaluation S (underlying X) A).functor ⋙ iterates S A f :=
  (SpanPayload.pasteIso (inverse S A f) (tagged S A f)).symm

theorem evaluation_paste (f : X ⟶ Y) : evaluationSquare S A f = pasted S A f := rfl

private theorem taggedComp (f : X ⟶ Y) (g : Y ⟶ Z) :
    Paste.CompLaw (X := leaves S A g) (Y := leaves S A f) (W := leaves S A (f ≫ g))
    (X' := iterates S A g) (Y' := iterates S A f) (W' := iterates S A (f ≫ g))
    (F := taggedEvaluation S A Z) (G := taggedEvaluation S A Y) (H := taggedEvaluation S A X)
    (tagged S A (f ≫ g)).symm (tagged S A g).symm (tagged S A f).symm
    (eqToHom (leafComp S A f g)) (eqToHom (iterateComp S A f g)) :=
  PayloadLaws.comp (U := leaves S A g) (V := leaves S A f) (W := leaves S A (f ≫ g))
    (U' := iterates S A g) (V' := iterates S A f) (W' := iterates S A (f ≫ g))
    (F := taggedEvaluation S A Z) (G := taggedEvaluation S A Y) (H := taggedEvaluation S A X)
    (tagged S A (f ≫ g)).symm (tagged S A g).symm (tagged S A f).symm
    (leafComp S A f g) (iterateComp S A f g) (taggedTransport S A (f ≫ g)) (taggedTransport S A g) (taggedTransport S A f)

/-- Covariant composition in execution order for arbitrary ambient strong maps. -/
private theorem pastedComp (f : X ⟶ Y) (g : Y ⟶ Z) : Paste.CompLaw (X := whole S A g) (Y := whole S A f) (W := whole S A (f ≫ g))
    (X' := iterates S A g) (Y' := iterates S A f) (W' := iterates S A (f ≫ g))
    (F := (evaluation S (underlying Z) A).functor) (G := (evaluation S (underlying Y) A).functor) (H := (evaluation S (underlying X) A).functor)
    (pasted S A (f ≫ g))
    (pasted S A g) (pasted S A f)
    (eqToHom (wholeComp S A f g)) (eqToHom (iterateComp S A f g)) :=
  Paste.compLaw (X := whole S A g) (Y := whole S A f) (W := whole S A (f ≫ g)) (X' := leaves S A g) (Y' := leaves S A f) (W' := leaves S A (f ≫ g))
    (X'' := iterates S A g) (Y'' := iterates S A f) (W'' := iterates S A (f ≫ g))
    (F := (PayloadLaws.All.presentation S A (underlying Z)).inverse) (G := (PayloadLaws.All.presentation S A (underlying Y)).inverse)
    (H := (PayloadLaws.All.presentation S A (underlying X)).inverse) (J := taggedEvaluation S A Z) (K := taggedEvaluation S A Y) (L := taggedEvaluation S A X)
    (inverse S A (f ≫ g)).symm
    (inverse S A g).symm (inverse S A f).symm
    (tagged S A (f ≫ g)).symm (tagged S A g).symm (tagged S A f).symm
    (eqToHom (wholeComp S A f g)) (eqToHom (leafComp S A f g)) (eqToHom (iterateComp S A f g))
    (inverseComp S A f g) (taggedComp S A f g)

theorem evaluationComp (f : X ⟶ Y) (g : Y ⟶ Z) : Paste.CompLaw (X := whole S A g) (Y := whole S A f) (W := whole S A (f ≫ g))
    (X' := iterates S A g) (Y' := iterates S A f) (W' := iterates S A (f ≫ g))
    (F := (evaluation S (underlying Z) A).functor) (G := (evaluation S (underlying Y) A).functor) (H := (evaluation S (underlying X) A).functor)
    (evaluationSquare S A (f ≫ g))
    (evaluationSquare S A g) (evaluationSquare S A f)
    (eqToHom (wholeComp S A f g)) (eqToHom (iterateComp S A f g)) := by
  rw [evaluation_paste S A (f ≫ g), evaluation_paste S A g, evaluation_paste S A f]
  exact pastedComp S A f g

end ContextualComposition.GrothendieckStep.TelescopeAmbientLaws
