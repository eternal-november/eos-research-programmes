module
public import ContextualComposition.AmbientFramedCells
public import ContextualComposition.AmbientInnerCellAtom
public import ContextualComposition.AmbientInsideUnitCell
public import ContextualComposition.AmbientConstraintRows
public import ContextualComposition.AmbientFlatInside
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientFunctorCorner
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
open AmbientFramedCells
variable {i j : Nat} (r : Map S i j) (a : obj S i X ⟶ obj S j X)
def Corner : Prop := tot (V := obj S i X) (W := obj S j X) a = global (S := S) (i := i) (j := j) (underlying X) r
theorem pin (h : tot a = global (S := S) (i := i) (j := j) (underlying X) r) : Corner X r a := h
end ContextualComposition.GrothendieckStep.AmbientFunctorCorner
