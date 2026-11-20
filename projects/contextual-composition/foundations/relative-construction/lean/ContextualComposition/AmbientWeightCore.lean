module
public import ContextualComposition.AmbientFlatInside
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientFlatWeight
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks FibreValue TelescopeSquares
open ContextadRoutes ContextadOuterCharts ContextadLawTransport AmbientBicategory AmbientCoordinates ContextadWeakAction AmbientModificationAction
open AmbientHorizontalRead AmbientHorizontalFrames ContextadInsideCells ContextadModification
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 650000
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable {X Y : Obj.{u,v} B} (f : X ⟶ Y)
attribute [local irreducible] BlockEvaluation.global ContextadAmbientPayload.totalStrong AmbientModificationAction.totalCell
variable {k i j : Nat} (r : Map S i j) (p : gradeCart r)
theorem splitRead (x : Raw S X (k+i)) :
    Aligned (atRaw (X := obj S i X) (Y := obj S j Y) (i := k) (j := k) S (cell S k (comparison S r p f).inv) ((splitAt X k i).obj x))
      ((splitAt Y k j).map ((AmbientComparisonRead.q S (inside k r) f).app x)) :=
  (AmbientComparisonRead.modAt S (comparison S r p f).inv k _).trans (AmbientInsideMateRead.read f k r p x).symm
set_option linter.defProp false in
def flat (F : Raw S X (k+i) ⥤ Total (underlying (obj S k (obj S i X))) (𝟭 B))
    (G : Raw S Y (k+j) ⥤ Total (underlying (obj S k (obj S j Y))) (𝟭 B)) [G.IsIso]
    (u : splitAt (S := S) (underlying X) k i ⋙ chart S (obj S i X) k = F)
    (v : splitAt (S := S) (underlying Y) k j ⋙ chart S (obj S j Y) k = G) :=
  let n := totalCell (cell S k (comparison S r p f).inv).hom.as
  let w := AmbientComparisonRead.q S (inside k r) f
  let z := splitRead (k := k) f r p
  AmbientFlatInside.rechart F G (chart S (obj S i X) k) (chart S (obj S j Y) k) (splitAt X k i) (splitAt Y k j) u v n w z
end ContextualComposition.GrothendieckStep.AmbientFlatWeight
