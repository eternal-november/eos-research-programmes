module
public import ContextualComposition.AmbientWeightPicture
public import ContextualComposition.AmbientFoldReading
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientCellPictures
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
open AmbientWeightPicture AmbientHorizontalRead ContextadInsideCells AmbientFlatInside
variable {k i j : Nat} {r s : Map S i j} (c : Cell r s)
variable {a b : obj S i X ⟶ obj S j X} (t : a ⟶ b)
variable (I : View (S := S) X k i) (J : View (S := S) X k j)
def Evidence : Prop :=
  letI := J.iso
  Picture I.F J.F (totalCell (cell S k t).hom.as) (rawCell (underlying X) (insideCell k c)).hom
theorem collect (h : Reads (S := S) (X := X) t c) (e : tot a = global X r) (w : tot b = global X s) :
    Evidence c t I J := by
  let _ := J.iso
  exact AmbientFlatInside.flat (k := k) X c t h e w I.F J.F I.commute J.commute
noncomputable def v3 (Z : Obj.{u,v} B) : View (S := S) Z 1 3 := ⟨chart S Z 4,BlockEvaluation.globalIso S (underlying Z) 4,AmbientDeepIndices.chart3 S Z⟩
end ContextualComposition.GrothendieckStep.AmbientCellPictures
