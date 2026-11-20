module
public import ContextualComposition.AmbientMateReindex
public import ContextualComposition.AmbientChartSplice
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientInsideMate
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite FibreValue TelescopeSquares
open ContextadAmbientPayload ContextadWeakAction AmbientBicategory AmbientCoordinates ContextadRoutes
open ContextadModification NativeBlocks CategoryTheory.Bicategory ContextadInsideCells ContextadLawTransport
open ContextadOuterCharts SpanApex AmbientBlockCells AmbientModificationAction AmbientHorizontalFrames AmbientMateReindex ContextadWeakWeight
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split} {X Y : Obj.{u,v} B}
variable (f : X ⟶ Y) (k : Nat) {i j : Nat} (r : Map S i j)
theorem qTail (x) :
    Aligned ((tailAt (S := S) (underlying Y) k j).map ((AmbientComparisonRead.q S (inside k r) f).app x))
      ((AmbientComparisonRead.q S r f).app ((tailAt (S := S) (underlying X) k i).obj x)) :=
  reindex f.hom (power S i).dest (power S j).dest r.grade r.leg (blocks S k i).rest (blocks S k j).rest
    (blocks S k i).dest (blocks S k j).dest (inside k r).grade (inside k r).leg
    (whiskTail X k r) (whiskTail Y k r) (ContextadInsideCells.leg k r) x
theorem chartAction (i : Nat) :
    atEndpoint f.hom (power S i).dest ⋙ chart S Y i = chart S X i ⋙ totalStrong (AmbientBicategory.map S i f).hom := by
  rw [show totalStrong (AmbientBicategory.map S i f).hom = _ from AmbientBlockIteration.encodedBlock S f.hom i]
  exact (ContextadRecognition.eraseInv _ _).symm
theorem splitAction (i : Nat) :
    atEndpoint f.hom (power S (k+i)).dest ⋙ splitAt (S := S) (underlying Y) k i =
      splitAt X k i ⋙ atEndpoint (AmbientBicategory.map S i f).hom (power S k).dest := by
  let H := atEndpoint f.hom (power S (k+i)).dest
  let G := atEndpoint (AmbientBicategory.map S i f).hom (power S k).dest
  apply BoundaryPaste.fold_ext
  · apply (congrArg (H ⋙ ·) (splitFront (S := S) (underlying Y) k i)).trans
    apply (congrArg (· ⋙ (blocks S k i).first) (actionGrade _ (totalStrong f.hom) (strongOver f.hom))).trans
    exact ((congrArg (splitAt (S := S) X k i ⋙ ·) (actionGrade (power S k).dest (totalStrong (AmbientBicategory.map S i f).hom) (strongOver (AmbientBicategory.map S i f).hom))).trans (splitFront (S := S) (underlying X) k i)).symm
  · apply (congrArg (H ⋙ ·) (splitTail (S := S) (underlying Y) k i)).trans
    apply (congrArg (· ⋙ chart S Y i) (actionPull f.hom (power S i).dest (blocks S k i).rest (blocks S k i).dest).symm).trans
    apply (congrArg (tailAt (S := S) (underlying X) k i ⋙ ·) (chartAction f i)).trans
    let T := totalStrong (AmbientBicategory.map S i f).hom
    have a := congrArg (fun z : Raw S X (k+i) ⥤ Total (underlying (obj S i X)) (𝟭 B) => z ⋙ T) (splitTail (S := S) (underlying X) k i).symm
    have b := congrArg (splitAt (S := S) (underlying X) k i ⋙ ·) (actionLeaf (power S k).dest T (strongOver (AmbientBicategory.map S i f).hom)).symm
    simp only [Functor.assoc] at a b ⊢
    exact a.trans b
end ContextualComposition.GrothendieckStep.AmbientInsideMate
