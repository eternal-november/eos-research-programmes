module
public import ContextualComposition.AmbientFoldedAssocPost
public import ContextualComposition.AmbientFoldedAssocCell
public import ContextualComposition.AmbientScheduleFragment
public import ContextualComposition.AmbientInsideUnitCell
public import ContextualComposition.AmbientConstraintRows
public import ContextualComposition.AmbientFlatInside
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientFoldedAssocRead
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
def cell := AmbientFoldedAssocCell.trace X (assoc S X d m C) C.assoc (AmbientConstraintRows.assoc X d m C) (outerTotal X m) (innerTotal X m)
set_option linter.defProp false in
def step := AmbientFoldedAssocPost.step X (assoc S X d m C) C.assoc m (cell X d m C)
end ContextualComposition.GrothendieckStep.AmbientFoldedAssocRead
