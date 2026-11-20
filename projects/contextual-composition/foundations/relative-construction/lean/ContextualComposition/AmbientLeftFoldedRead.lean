module
public import ContextualComposition.AmbientLeftFoldedPost
public import ContextualComposition.AmbientLeftFoldedCell
public import ContextualComposition.AmbientScheduleFragment
public import ContextualComposition.AmbientInsideUnitCell
public import ContextualComposition.AmbientConstraintRows
public import ContextualComposition.AmbientFlatInside
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientLeftFoldedRead
open CategoryTheory CategoryTheory.Functor CategoryTheory.Bicategory TelescopeSquares
open AmbientBicategory AmbientCoordinates AmbientHorizontalDiagrams AmbientFoldFrames AmbientHorizontalRead AmbientLetterRead
open ContextadRoutes ContextadLawTransport ContextadInsideCells NativeBlocks
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 650000
attribute [local irreducible] BlockEvaluation.global AmbientModificationAction.totalCell ContextadAmbientPayload.totalStrong
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (X : Obj.{u,v} B)
open AmbientHorizontalFrames AmbientNativeLetterFrame
open ContextadNativeLaws AmbientLiftedLetters
variable (d : ContextadUnit.Data P) (m : ContextadTotal.Native S) (C : Constraints d m)
set_option linter.defProp false in
def cell := AmbientLeftFoldedCell.trace X (left S X d m C) C.left (AmbientConstraintRows.left X d m C) (firstTotal X d m) (idTotal (S := S) X 1)
set_option linter.defProp false in
def step := AmbientLeftFoldedPost.step X (left S X d m C) C.left m (cell X d m C)
end ContextualComposition.GrothendieckStep.AmbientLeftFoldedRead
