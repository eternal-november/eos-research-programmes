module
public import ContextualComposition.AmbientBoundaryReduction
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientSquareGuard
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
variable {i j : Nat} {a b : obj S i X ⟶ obj S j Y}
def Guard (r : Map S i j) (t : a ≅ b) : Prop := RRead (i := i) (j := j) S f t r
theorem pack (r : Map S i j) (t : a ≅ b) (h : RRead (i := i) (j := j) S f t r) : Guard f r t := h
theorem unpack (r : Map S i j) (t : a ≅ b) (h : Guard f r t) : RRead (i := i) (j := j) S f t r := h
end ContextualComposition.GrothendieckStep.AmbientSquareGuard
