module
public import ContextualComposition.AmbientWeightPicture
public import ContextualComposition.AmbientFoldReading
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientWeightUnpack
open CategoryTheory CategoryTheory.Functor CategoryTheory.Bicategory TelescopeSquares
open NativeBlocks ContextadRoutes ContextadLawTransport ContextadModification ContextadNativeLaws ContextadOuterCharts
open AmbientCoordinates AmbientBicategory AmbientHorizontalFrames AmbientHorizontalDiagrams AmbientHorizontalNaturality AmbientFoldReading AmbientFlatWeight
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 650000
attribute [local irreducible] BlockEvaluation.global AmbientModificationAction.totalCell ContextadAmbientPayload.totalStrong
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable {X Y : Obj.{u,v} B} (f : X ⟶ Y)
open AmbientWeightLetters AmbientModificationAction
open AmbientWeightPicture
variable {a b : obj S 3 X ⟶ obj S 2 Y} (t : a ⟶ b) (r : Map S 3 2)
def Diagram : Prop :=
  let J := v1 (S := S) Y
  letI := J.iso
  Picture (v2 (S := S) X).F J.F (totalCell t.hom.as) (AmbientComparisonRead.q S r f)
theorem extract (h : Diagram f t r) : QRead (i := 3) (j := 2) f r t := h
end ContextualComposition.GrothendieckStep.AmbientWeightUnpack
