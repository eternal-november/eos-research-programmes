module
public import ContextualComposition.AmbientInsideMulWeight
public import ContextualComposition.AmbientOutsideWeightRead
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientSuccessorMap
open CategoryTheory CategoryTheory.Functor CategoryTheory.Bicategory
open AmbientBicategory AmbientCoordinates AmbientHorizontalFrames AmbientHorizontalDiagrams AmbientHorizontalNaturality
open AmbientBoundaryReduction AmbientSquareBridge ContextadRoutes ContextadNativeLaws ContextadLawTransport ContextadModification
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1550000
attribute [local irreducible] BlockEvaluation.global AmbientModificationAction.totalCell ContextadAmbientPayload.totalStrong
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable {X Y : Obj.{u,v} B} (f : X ⟶ Y) (m : ContextadTotal.Native S)
theorem succ (n : Nat) : K S (X := obj S n X) (Y := obj S n Y) (AmbientBicategory.map S n f) = AmbientBicategory.map S (n+1) f :=
  InducedBicategory.hom_ext (AmbientBlockIteration.blockSucc S f.hom n)
theorem lift {n : Nat} (a : obj S n X ⟶ obj S n Y) (e : a = AmbientBicategory.map S n f) :
    K S (X := obj S n X) (Y := obj S n Y) a = AmbientBicategory.map S (n+1) f :=
  (congrArg (fun z : obj S n X ⟶ obj S n Y => K S z) e).trans (succ f n)
end ContextualComposition.GrothendieckStep.AmbientSuccessorMap
