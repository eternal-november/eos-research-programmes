module
public import ContextualComposition.AmbientSuffixView
public import ContextualComposition.AmbientSuffixCells
public import ContextualComposition.AmbientFlatInside
public import ContextualComposition.AmbientBoundaryReduction
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientSuffixCellView
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
variable {i j : Nat} {r s : Map S i j} (c : Cell r s) (Z : Obj.{u,v} B)
variable {a b : obj S i (obj S 1 Z) ⟶ obj S j (obj S 1 Z)} (t : a ⟶ b)
variable (I : Chart (S := S) Z i) (J : Chart (S := S) Z j)
def Viewed : Prop :=
  letI := J.iso
  ∀ x, Aligned (J.F.strictInv.map ((totalCell t.hom.as).app (I.F.obj x))) ((AmbientSuffixCells.outer (S := S) (asApex c) Z).hom.app x)
theorem carry (h : Reads (S := S) (X := obj S 1 Z) t c) : Viewed c Z t I J := by
  let _ := J.iso
  exact AmbientFlatInside.rechart I.F J.F (chart S (obj S 1 Z) i) (chart S (obj S 1 Z) j)
    (stage (S := S) (underlying Z) _) (stage (S := S) (underlying Z) _) I.commute J.commute
    (totalCell t.hom.as) (AmbientSuffixCells.outer (S := S) (asApex c) Z).hom fun x => (h _).trans (AmbientSuffixCells.staged (asApex c) Z x).symm
end ContextualComposition.GrothendieckStep.AmbientSuffixCellView
