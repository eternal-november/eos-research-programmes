module
public import ContextualComposition.AmbientSuffixCellView
public import ContextualComposition.AmbientDisjointFrames
public import ContextualComposition.AmbientSuffixCells
public import ContextualComposition.AmbientFlatInside
public import ContextualComposition.AmbientBoundaryReduction
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientSuffixLetters
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
variable (Z : Obj.{u,v} B)
noncomputable def v3 : Chart (S := S) Z 3 := ⟨chart S Z 4,BlockEvaluation.globalIso S (underlying Z) 4,AmbientDisjointFrames.resolve3 S Z⟩
section Two
variable {r s : Map S 1 1} (c : Cell r s) {a b : obj S 1 (obj S 1 Z) ⟶ obj S 1 (obj S 1 Z)} (t : a ⟶ b)
theorem two (h : Reads (S := S) (X := obj S 1 Z) (j := 1) (k := 1) t c) :
    Reads (S := S) (X := Z) (j := 2) (k := 2) (r := suffix r) (s := suffix s) t (suffixCell c) :=
  AmbientSuffixCellView.carry c Z t (v1 Z) (v1 Z) h
end Two
section Four
variable {r s : Map S 3 1} (c : Cell r s) {a b : obj S 3 (obj S 1 Z) ⟶ obj S 1 (obj S 1 Z)} (t : a ⟶ b)
theorem four (h : Reads (S := S) (X := obj S 1 Z) (j := 3) (k := 1) t c) :
    Reads (S := S) (X := Z) (j := 4) (k := 2) (r := suffix r) (s := suffix s) t (suffixCell c) :=
  AmbientSuffixCellView.carry c Z t (v3 Z) (v1 Z) h
end Four
end ContextualComposition.GrothendieckStep.AmbientSuffixLetters
