module
public import ContextualComposition.AmbientShiftBoundary
public import ContextualComposition.AmbientLetterRead
public import ContextualComposition.AmbientSuffixCells
public import ContextualComposition.AmbientFlatInside
public import ContextualComposition.AmbientBoundaryReduction
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientOutsideLetters
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite FibreValue TelescopeSquares
open ContextadAmbientPayload ContextadWeakAction AmbientBicategory AmbientCoordinates ContextadRoutes
open ContextadModification NativeBlocks CategoryTheory.Bicategory ContextadLawTransport ContextadOuterCharts
open SpanApex AmbientBlockCells AmbientModificationAction AmbientHorizontalFrames ContextadWeakWeight AmbientInsideMateRead
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 550000
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split} {X Y : Obj.{u,v} B}
open AmbientSuffixRoutes AmbientBoundaryReduction
attribute [local irreducible] BlockEvaluation.global ContextadAmbientPayload.totalStrong AmbientModificationAction.totalCell stage
open AmbientSuffixView AmbientHorizontalRead ContextadAppendCells
open ContextadNativeLaws AmbientHorizontalDiagrams
variable (Z : Obj.{u,v} B) (d : ContextadUnit.Data P) (m : ContextadTotal.Native S) (C : Constraints d m)
set_option linter.defProp false in
def right := AmbientShiftBoundary.two Z C.right (AmbientHorizontalFrames.right S (obj S 1 Z) d m C) (AmbientConstraintRows.right (obj S 1 Z) d m C)
set_option linter.defProp false in
def assoc := AmbientShiftBoundary.four Z C.assoc (AmbientHorizontalFrames.assoc S (obj S 1 Z) d m C) (AmbientConstraintRows.assoc (obj S 1 Z) d m C)
end ContextualComposition.GrothendieckStep.AmbientOutsideLetters
