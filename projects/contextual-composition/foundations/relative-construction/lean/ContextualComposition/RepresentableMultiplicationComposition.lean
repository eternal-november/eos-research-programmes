module
public import ContextualComposition.RepresentableMultiplicationPaste
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableMultiplicationComposition
open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Pseudofunctor
open AmbientBicategory AmbientHorizontalFrames AmbientHorizontalDiagrams AmbientCoherentPseudomonad
open AmbientCoordinates ContextadModification ContextadRoutes ContextadNativeLaws ContextadOuterCharts
open RepresentableMultiplicationFrame
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 850000
attribute [local irreducible] BlockEvaluation.global ContextadAmbientPayload.totalStrong AmbientModificationAction.totalCell
open RepresentableMultiplicationPaste
universe u
variable {B : Type u} [Category.{u} B] {P : Endpoints.{u,u,u,u} B} {S : P.Split} (T : Data S)
variable {X Y Z : Obj.{u,u} B} (f : X ⟶ Y) (g : Y ⟶ Z)
noncomputable abbrev cmp₂ {I J : Obj.{u,u} B} (j : I ⟶ J) := comparison S (tensor T.mult) T.mult.cart j
noncomputable abbrev F₁ : StrictPseudofunctor (Obj.{u,u} B) (Obj.{u,u} B) := action S 1
noncomputable abbrev F₂ : StrictPseudofunctor (Obj.{u,u} B) (Obj.{u,u} B) := action S 2
theorem opPaste {i j : Nat} (r : ContextadRoutes.Map S i j) (p : gradeCart r) :
    comparison S r p (f ≫ g) = paste (AmbientBicategory.comp S i f g) (AmbientBicategory.comp S j f g).symm
      (comparison S r p f) (comparison S r p g) := by
  rw [AmbientOperationLaws.composition S r p f g]
  apply Iso.ext
  simp only [AmbientOperationLaws.paste,paste,Iso.trans_hom,Iso.symm_hom,whiskerRightIso_hom,whiskerLeftIso_hom,
    Strict.associator_eqToIso,eqToIso.hom,eqToIso.inv,eqToHom_trans,eqToHom_trans_assoc]
theorem nativePaste :
    cmp₂ T (f ≫ g) = paste (AmbientBicategory.comp S 2 f g) (AmbientBicategory.comp S 1 f g).symm (cmp₂ T f) (cmp₂ T g) :=
  opPaste f g (tensor T.mult) T.mult.cart
theorem comp₂ :
    K S (K S (f ≫ g)) = K S (K S f) ≫ K S (K S g) :=
  (congrArg (K S) (AmbientBicategory.comp S 1 f g)).trans (AmbientBicategory.comp S 1 (K S f) (K S g))
set_option linter.defProp false in
def rawShift :=
  shiftPaste (a := obj S 2 X) (b := obj S 2 Y) (c := obj S 2 Z) (x := obj S 1 X) (y := obj S 1 Y) (z := obj S 1 Z)
    (twice S f) (twice S g) (twice S (f ≫ g)) (comp₂ f g) (AmbientBicategory.comp S 2 f g)
    (AmbientBicategory.comp S 1 f g).symm (cmp₂ T f) (cmp₂ T g)
theorem original :
    squareM S T.mult (f ≫ g) = paste (comp₂ f g) (AmbientBicategory.comp S 1 f g).symm (squareM S T.mult f) (squareM S T.mult g) := by
  change shift (M S Z T.mult) (twice S (f ≫ g)) (cmp₂ T (f ≫ g)) = _
  rw [nativePaste T f g]
  exact rawShift T f g
end ContextualComposition.GrothendieckStep.RepresentableMultiplicationComposition
