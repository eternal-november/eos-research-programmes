module
public import ContextualComposition.RepresentablePureGenericAssembly
public import ContextualComposition.RepresentablePureOriginalAssoc
public import ContextualComposition.RepresentablePureActualUnits
public import ContextualComposition.RepresentablePureKleisli
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentablePurePseudofunctor
open CategoryTheory CategoryTheory.Bicategory
open AmbientBicategory AmbientCoherentPseudomonad RepresentableKleisli
open RepresentableKleisliCoherent RepresentableKleisliBicategory RepresentableKleisliConstraints
open RepresentablePureOriginalPorts RepresentablePureActualUnits RepresentableKleisliOriginal
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 600000
attribute [local irreducible] BlockEvaluation.global ContextadAmbientPayload.totalStrong AmbientModificationAction.totalCell
universe u
variable {B : Type u} [Category.{u} B]
abbrev Core (B : Type u) := RepresentablePureGenericAssembly.Core B
noncomputable instance coreCategory : Category (Core B) :=
  RepresentablePureGenericAssembly.coreCategory (@yObj B _)

noncomputable def pureBaseFunctor : B ⥤ Core B where
  obj A := ⟨A⟩
  map f := pureMap f
  map_id A := RepresentablePure.pure_id A
  map_comp f g := RepresentablePure.pure_comp f g

variable {P : Endpoints.{u,u,u,u} B} {S : P.Split} (T : Data S)
variable {A C : B}
noncomputable abbrev leftPort : RepresentablePureGenericAssembly.Left (@yObj B _) (action.{u,u} S 1) (μ T) (eta T) :=
  fun {_ _} f => leftUnit T f
noncomputable abbrev rightPort : RepresentablePureGenericAssembly.Right (@yObj B _) (action.{u,u} S 1) (μ T) (eta T) :=
  fun {_ _} f => rightUnit T f
noncomputable abbrev assocPort : RepresentablePureGenericAssembly.Assoc (@yObj B _) (action.{u,u} S 1) (μ T) :=
  fun {_ _ _ _} f g h => reassociate T f g h

theorem rawFaces :
    RepresentablePureGenericAssembly.RawFaces (@yObj B _) (action.{u,u} S 1) (μ T) (eta T) (ell T)
      (leftPort T) (rightPort T) (assocPort T) where
  association := @RepresentablePureOriginalAssoc.original B _ P S T
  left := @unitLeftOriginal B _ P S T
  right := @unitRightOriginal B _ P S T

noncomputable def faces : RepresentablePureBuilder.Faces (A := Core B) (ops T) :=
  RepresentablePureGenericAssembly.faces (@yObj B _) (action.{u,u} S 1) (μ T) (eta T) (ell T)
    (leftPort T) (rightPort T) (assocPort T) (rawFaces T)

noncomputable def bridge : @Pseudofunctor (LocallyDiscrete (Core B)) _ (Part B) (bicategory T) :=
  RepresentablePureBuilder.buildPure (laws T (actualLast T) (actualPent T)) (faces T)

/-- Ordinary-base pure maps in the actual representable Kleisli bicategory. -/
noncomputable def pure : @Pseudofunctor (LocallyDiscrete B) _ (Part B) (bicategory T) :=
  letI : Bicategory (Part B) := bicategory T
  (pureBaseFunctor (B := B)).toPseudofunctor.comp (bridge T)

theorem pureObjAt (A : B) :
    letI : Bicategory (Part B) := bicategory T
    (pure T).obj (LocallyDiscrete.mk A) = (⟨A⟩ : Part B) := rfl

theorem pureMapAt (f : A ⟶ C) :
    letI : Bicategory (Part B) := bicategory T
    (pure T).map (show (LocallyDiscrete.mk A) ⟶ (LocallyDiscrete.mk C) from f.toLoc) = pureK T f := rfl
end ContextualComposition.GrothendieckStep.RepresentablePurePseudofunctor
