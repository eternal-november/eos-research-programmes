module
public import ContextualComposition.AmbientWeightCore
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
structure View (X : Obj.{u,v} B) (k i : Nat) where
  F : Raw S X (k+i) ⥤ Total (underlying (obj S k (obj S i X))) (𝟭 B)
  iso : F.IsIso
  commute : splitAt (S := S) (underlying X) k i ⋙ chart S (obj S i X) k = F
noncomputable def v0 (X : Obj.{u,v} B) : View (S := S) X 1 0 := ⟨chart S X 1,BlockEvaluation.globalIso S (underlying X) 1,splitOne0 X⟩
noncomputable def v1 (X : Obj.{u,v} B) : View (S := S) X 1 1 := ⟨chart S X 2,BlockEvaluation.globalIso S (underlying X) 2,splitOne1 X⟩
noncomputable def v2 (X : Obj.{u,v} B) : View (S := S) X 1 2 := ⟨chart S X 3,BlockEvaluation.globalIso S (underlying X) 3,splitOne2 X⟩
def Viewed {k i j : Nat} (r : Map S i j) (p : gradeCart r) (I : View (S := S) X k i) (J : View (S := S) Y k j) : Prop :=
  letI := J.iso
  ∀ x, Aligned (J.F.strictInv.map ((totalCell (cell S k (comparison S r p f).inv).hom.as).app (I.F.obj x)))
    ((AmbientComparisonRead.q S (inside k r) f).app x)
theorem reading {k i j : Nat} (r : Map S i j) (p : gradeCart r) (I : View (S := S) X k i) (J : View (S := S) Y k j) : Viewed f r p I J := by
  letI := J.iso
  exact flat (k := k) f r p I.F J.F I.commute J.commute
theorem unitView (r : Map S 0 1) (p : gradeCart r) : Viewed f r p (v0 X) (v1 Y) := reading f r p _ _
theorem muView (r : Map S 2 1) (p : gradeCart r) : Viewed f r p (v2 X) (v1 Y) := reading f r p _ _
end ContextualComposition.GrothendieckStep.AmbientFlatWeight
