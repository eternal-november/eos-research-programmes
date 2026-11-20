module
public import ContextualComposition.RepresentableLastAnchor
public import ContextualComposition.RepresentableKleisliOriginal
public import ContextualComposition.RepresentableKleisliPentagon
public import ContextualComposition.RepresentableMultiplicationFrame
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableOriginalLastAssoc
open CategoryTheory CategoryTheory.Bicategory
open AmbientBicategory AmbientHorizontalFrames AmbientHorizontalDiagrams AmbientCoherentPseudomonad
open AmbientCoordinates ContextadRoutes RepresentableMultiplicationFrame
open RepresentableKleisli RepresentableKleisliOriginal RepresentableKleisliConstraints
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1850000
attribute [local irreducible] BlockEvaluation.global ContextadAmbientPayload.totalStrong AmbientModificationAction.totalCell
universe u
variable {B : Type u} [Category.{u} B] {P : Endpoints.{u,u,u,u} B} {S : P.Split} (T : Data S)
noncomputable abbrev dShift {X Y : Obj.{u,u} B} (f : X ⟶ Y) :=
  shift (M.{u,u} S Y T.mult) (twice.{u,u} S f) (comparison.{u,u} S (tensor T.mult) T.mult.cart f)
theorem dPin {X Y : Obj.{u,u} B} (f : X ⟶ Y) : dShift T f = D T f := (squareShift T f).symm
variable {V W X Y : B}
variable (f : KH S V W) (g : KH S W X) {h h' : KH S X Y} (t : h ⟶ h')
set_option linter.defProp false in
def rawLast :=
  RepresentableLastAnchor.withNative (V := yObj V) (W := yObj W) (X := yObj X) (Y := yObj Y)
    (action.{u,u} S 1) (μ T) (D T) (a T) f g t
    (AmbientBicategory.cell.{u,u} S 1 t) (AmbientBicategory.cell.{u,u} S 1 (AmbientBicategory.cell.{u,u} S 1 t))
    (M.{u,u} S (yObj X) T.mult) (M.{u,u} S (KObj S Y) T.mult)
    (AmbientBicategory.cell.{u,u} S 2 t) (twice.{u,u} S h) (twice.{u,u} S h')
    (comparison.{u,u} S (tensor T.mult) T.mult.cart h) (comparison.{u,u} S (tensor T.mult) T.mult.cart h')
    rfl rfl rfl rfl (heq_of_eq (dPin T h)) (heq_of_eq (dPin T h'))
    (iterateCell t) (AmbientOperationLaws.modification.{u,u} S (tensor T.mult) T.mult.cart t)
theorem original :
    composeCell T (𝟙 (compose T f g)) t ≫ (reassociate T f g h').hom =
    (reassociate T f g h).hom ≫ composeCell T (𝟙 f) (composeCell T (𝟙 g) t) := by
  let eqn (A : RepresentableKleisliPentagon.Assocs T) : Prop :=
    composeCell T (𝟙 (compose T f g)) t ≫ (A f g h').hom =
      (A f g h).hom ≫ composeCell T (𝟙 f) (composeCell T (𝟙 g) t)
  have H : eqn (RepresentableKleisliPentagon.genericBend T) := rawLast T f g t
  exact (congrArg eqn (RepresentableKleisliPentagon.family T)).mp H
end ContextualComposition.GrothendieckStep.RepresentableOriginalLastAssoc
