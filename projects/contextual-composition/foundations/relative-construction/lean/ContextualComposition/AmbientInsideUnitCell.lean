module
public import ContextualComposition.AmbientFlatInside
public import ContextualComposition.AmbientLetterTotals
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientInsideUnitCell
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks FibreValue TelescopeSquares
open ContextadRoutes ContextadOuterCharts ContextadLawTransport AmbientBicategory AmbientCoordinates ContextadWeakAction AmbientModificationAction
open AmbientHorizontalRead AmbientHorizontalFrames ContextadInsideCells
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (X : Obj.{u,v} B)
attribute [local irreducible] BlockEvaluation.global ContextadAmbientPayload.totalStrong AmbientModificationAction.totalCell ContextadLawTransport.rawCell ContextadInsideCells.insideCell
variable {i : Nat} {r s : Map S i 1} {a b : obj S i X ⟶ obj S 1 X} (c : Cell r s) (t : a ⟶ b)
section Unit
variable {r s : Map S 1 1} {a b : obj S 1 X ⟶ obj S 1 X} (c : Cell r s) (t : a ⟶ b)
theorem unit (h : Reads (S := S) (X := X) t c) (e : tot a = global X r) (w : tot b = global X s) :
    Reads (S := S) (X := X) (j := 2) (k := 2) (cell S 1 t) (insideCell 1 c) :=
  AmbientFlatInside.unitLetter X c t h e w
end Unit
end ContextualComposition.GrothendieckStep.AmbientInsideUnitCell
