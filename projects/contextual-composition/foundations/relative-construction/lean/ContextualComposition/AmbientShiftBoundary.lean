module
public import ContextualComposition.AmbientSuffixLetters
public import ContextualComposition.AmbientConstraintRows
public import ContextualComposition.AmbientDisjointFrames
public import ContextualComposition.AmbientSuffixCells
public import ContextualComposition.AmbientFlatInside
public import ContextualComposition.AmbientBoundaryReduction
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientShiftBoundary
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
open AmbientNativeLetterFrame
variable (Z : Obj.{u,v} B)
section Two
variable {r s : Map S 1 1} (c : Cell r s) {a b : obj S 1 (obj S 1 Z) ⟶ obj S 1 (obj S 1 Z)} (t : a ≅ b)
def Two : Prop := Reads (S := S) (X := Z) (j := 2) (k := 2) (r := suffix r) (s := suffix s) t.hom (suffixCell c)
theorem two (h : Native (i := 1) (j := 1) (obj S 1 Z) c t) : Two Z c t :=
  AmbientSuffixLetters.two Z c t.hom h
end Two
section Four
variable {r s : Map S 3 1} (c : Cell r s) {a b : obj S 3 (obj S 1 Z) ⟶ obj S 1 (obj S 1 Z)} (t : a ≅ b)
def Four : Prop := Reads (S := S) (X := Z) (j := 4) (k := 2) (r := suffix r) (s := suffix s) t.hom (suffixCell c)
theorem four (h : Native (i := 3) (j := 1) (obj S 1 Z) c t) : Four Z c t :=
  AmbientSuffixLetters.four Z c t.hom h
end Four
end ContextualComposition.GrothendieckStep.AmbientShiftBoundary
