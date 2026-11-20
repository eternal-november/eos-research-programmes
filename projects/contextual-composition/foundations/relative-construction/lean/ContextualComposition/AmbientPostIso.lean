module
public import ContextualComposition.AmbientIsoFragments
public import ContextualComposition.AmbientOutsideLetters
public import ContextualComposition.AmbientFourToTwo
public import ContextualComposition.AmbientHorizontalDiagrams
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientPostIso
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite TelescopeSquares FibreValue
open AmbientBicategory AmbientCoordinates ContextadModification NativeBlocks CategoryTheory.Bicategory
open ContextadRoutes ContextadNativeLaws ContextadOuterCharts AmbientHorizontalFrames ContextadLawTransport
open ContextadCellWhisker ContextadCellPasting ContextadHorizontalLaws AmbientHorizontalRead ContextadWeakAction ContextadAmbientPayload AmbientHorizontalDiagrams
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 750000
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
open AmbientLetterRead
attribute [local irreducible] BlockEvaluation.global ContextadAmbientPayload.totalStrong AmbientModificationAction.totalCell
open AmbientNativeLetterFrame ContextadAppendCells
variable (X : Obj.{u,v} B) {n : Nat}
variable {r s : Map S n 2} (c : Cell r s) {a b : obj S n X ⟶ obj S 2 X} (t : a ≅ b) (m : ContextadTotal.Native S)
theorem read (h : Reads (S := S) (X := X) (j := n) (k := 2) t.hom c) :
    AmbientIsoFragments.At X (edge (after c (tensor m))) (whiskerRightIso t (M S X m)) :=
  AmbientIsoFragments.whisk (n := n) X (edge (after c (tensor m))) t (M S X m) (AmbientScheduleFragment.post (n := n) X c t.hom m h)
end ContextualComposition.GrothendieckStep.AmbientPostIso
