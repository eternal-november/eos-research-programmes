module
public import ContextualComposition.RepresentablePureOriginalPorts
public import ContextualComposition.RepresentablePureAssocAnchor
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentablePureOriginalAssoc
open CategoryTheory CategoryTheory.Bicategory
open AmbientBicategory AmbientHorizontalFrames AmbientHorizontalDiagrams AmbientCoherentPseudomonad
open RepresentableKleisli RepresentableKleisliOriginal RepresentableKleisliConstraints
open RepresentablePureAssociativity RepresentablePureOriginalPorts
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
attribute [local irreducible] BlockEvaluation.global ContextadAmbientPayload.totalStrong AmbientModificationAction.totalCell
universe u
variable {B : Type u} [Category.{u} B] {P : Endpoints.{u,u,u,u} B} {S : P.Split} (T : Data S)
variable {A C E J : B}
variable (f : yObj A ⟶ yObj C) (g : yObj C ⟶ yObj E) (h : yObj E ⟶ yObj J)
set_option linter.defProp false in
def raw :=
  RepresentablePureAssocAnchor.framed (X := yObj A) (Y := yObj C) (Z := yObj E) (W := yObj J)
    (action.{u,u} S 1) (μ T) (eta T) (ell T) (D T) (a T) f g h
    (C₀ T g h)
    (composeCell T (𝟙 (unit T C)) (C₀ T g h).hom)
    (leftUnit T (compose T (J₀ T g) (J₀ T h))) (leftUnit T (J₀ T (g ≫ h)))
    rfl rfl rfl rfl
    (RepresentableLeftUnitor.original T (A := C) (D := J)
      (f := compose T (J₀ T g) (J₀ T h)) (g := J₀ T (g ≫ h)) (C₀ T g h).hom)
    (leftCoherence T (J₀ T g) (J₀ T h))
theorem original :
    reassociate T (J₀ T f) (J₀ T g) (J₀ T h) ≪≫ ws (action S 1) (μ T) (J₀ T f) (C₀ T g h) ≪≫ C₀ T f (g ≫ h) =
      wr (action S 1) (μ T) (C₀ T f g) (J₀ T h) ≪≫ C₀ T (f ≫ g) h ≪≫ whiskerRightIso (α_ f g h) (unit T J) := by
  let eqn (A₀ : RepresentableKleisliPentagon.Assocs T) : Prop :=
    A₀ (J₀ T f) (J₀ T g) (J₀ T h) ≪≫ ws (action S 1) (μ T) (J₀ T f) (C₀ T g h) ≪≫ C₀ T f (g ≫ h) =
      wr (action S 1) (μ T) (C₀ T f g) (J₀ T h) ≪≫ C₀ T (f ≫ g) h ≪≫ whiskerRightIso (α_ f g h) (unit T J)
  have H : eqn (RepresentableKleisliPentagon.genericBend T) := raw T f g h
  exact (congrArg eqn (RepresentableKleisliPentagon.family T)).mp H
end ContextualComposition.GrothendieckStep.RepresentablePureOriginalAssoc
