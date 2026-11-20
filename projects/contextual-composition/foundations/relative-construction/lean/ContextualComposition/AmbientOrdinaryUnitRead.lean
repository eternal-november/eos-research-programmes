module
public import ContextualComposition.AmbientSuffixView
public import ContextualComposition.AmbientFoldReading
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientOrdinaryUnitRead
open CategoryTheory CategoryTheory.Functor CategoryTheory.Bicategory TelescopeSquares
open NativeBlocks ContextadRoutes ContextadLawTransport ContextadModification ContextadNativeLaws ContextadOuterCharts
open AmbientCoordinates AmbientBicategory AmbientHorizontalFrames AmbientHorizontalDiagrams AmbientHorizontalNaturality AmbientFoldReading
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 650000
attribute [local irreducible] BlockEvaluation.global AmbientModificationAction.totalCell ContextadAmbientPayload.totalStrong
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable {X Y : Obj.{u,v} B} (f : X ⟶ Y)
open AmbientBoundaryReduction
variable (d : ContextadUnit.Data P)
theorem unit : RRead (i := 0) (j := 1) S f (squareE S d f) (insert S d) := by
  intro x
  simp only [squareE,Iso.trans_inv,eqToIso.inv,compAt]
  let e := (congrArg (· ≫ E S Y d) (InducedBicategory.hom_ext (AmbientBlockIteration.blockZero S f.hom)).symm).symm
  obtain ⟨j,w⟩ := castAt (X := X) (Y := Y) (i := 0) (j := 1) S e x
  rw [w]
  exact (Aligned.trailing _ j).trans (AmbientComparisonRead.comparisonAt S (insert S d) (unitCart d) f x)
end ContextualComposition.GrothendieckStep.AmbientOrdinaryUnitRead
