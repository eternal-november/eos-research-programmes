module
public import ContextualComposition.RepresentablePureOriginalPorts
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentablePureActualUnits
open CategoryTheory CategoryTheory.Bicategory
open AmbientBicategory AmbientHorizontalFrames AmbientHorizontalDiagrams AmbientCoherentPseudomonad
open RepresentableKleisli RepresentableKleisliOriginal RepresentableKleisliBicategory RepresentableKleisliConstraints
open RepresentablePureAssociativity RepresentablePureUnits RepresentablePureOriginalPorts
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
attribute [local irreducible] BlockEvaluation.global ContextadAmbientPayload.totalStrong AmbientModificationAction.totalCell
universe u
variable {B : Type u} [Category.{u} B] {P : Endpoints.{u,u,u,u} B} {S : P.Split} (T : Data S)
theorem unitRightOriginal (f : yObj A ⟶ yObj B₀) :
    C₀ T f (𝟙 (yObj B₀)) ≪≫ whiskerRightIso (ρ_ f) (unit T B₀) =
      ws (action S 1) (μ T) (J₀ T f) (I₀ T B₀) ≪≫ rightUnit T (J₀ T f) := by
  have a₁ := rightPreStrict (X := yObj A) (Y := yObj B₀) (action.{u,u} S 1) (μ T) (eta T) (ell T) f
  have a₂ := rightReady (X := yObj A) (Y := yObj B₀) (action.{u,u} S 1) (μ T) (eta T) (ell T) f (rightIso T (yObj B₀)) (etaUnits T B₀)
  exact a₁.trans (congrArg (fun j => ws (action S 1) (μ T) (J₀ T f) (I₀ T B₀) ≪≫ j) a₂)
theorem unitLeftOriginal (f : yObj A ⟶ yObj B₀) :
    C₀ T (𝟙 (yObj A)) f ≪≫ whiskerRightIso (λ_ f) (unit T B₀) =
    wr (action S 1) (μ T) (I₀ T A) (J₀ T f) ≪≫ leftUnit T (J₀ T f) :=
  RepresentablePureUnits.left (action.{u,u} S 1) (μ T) (eta T) (ell T) f
end ContextualComposition.GrothendieckStep.RepresentablePureActualUnits
