module
public import ContextualComposition.AmbientDeepIndices
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientDisjointFrames
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite SpanApex TelescopeSquares FibreValue
open AmbientBicategory AmbientCoordinates ContextadModification NativeBlocks CategoryTheory.Bicategory
open ContextadRoutes ContextadNativeLaws ContextadOuterCharts AmbientHorizontalFrames ContextadLawTransport
open ContextadCellWhisker ContextadHorizontalLaws ContextadWeakAction ContextadAmbientPayload AmbientHorizontalDiagrams AmbientDeepIndices
open ContextadOuterRigidity ContextadChartDescent ContextadDisjointCut
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 650000
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split)
variable (X : Obj.{u,v} B)
theorem readyAfter (n : Nat) : stage (S := S) (underlying X) (power S (n+1)) = splitAt (S := S) X (n+1) 1 := by
  apply BoundaryPaste.fold_ext
  · exact (stageHead (S := S) X _).trans ((congrArg (gradeProjection (Y := underlying X) (e := (power S (n+1+1)).dest) ⋙ ·) (frontOne (S := S) (n+1)).symm).trans (splitFront (S := S) X (n+1) 1).symm)
  · have t := NativePacked.Lift.total_eq (underlying X) (e := (power S (n+1+1)).dest) (d := SpanApex.right P S) (H := NativeAssoc.last S (n+1)) (J := (blocks S (n+1) 1).rest) (h := rfl) (k := (blocks S (n+1) 1).dest) (tailOne (S := S) (n+1)).symm
    exact (stageLeaf (S := S) X _).trans ((congrArg (· ⋙ BlockEvaluation.global S X 1) t).trans (splitTail (S := S) X (n+1) 1).symm)
def resolve3 :=
  (congrArg (· ⋙ chart S (obj S 1 X) 3) (readyAfter S X 2)).trans ((splitTransport (S := S) X 3 1).trans (selfTransport (G := PackedFree.pow S X 4) (chart S X 4) (PackedCuts.sameLength S X (3,1)).symm))
section Span
variable {U V : NativeBlocks.Span (B := B)} (r : Operation U V)
variable {C D : Type*} [Category* C] [Category* D]
variable {J : Total (LY (S := S) (underlying X)) U.dest ⥤ C} {K : Total (LY (S := S) (underlying X)) V.dest ⥤ D}
variable {W : Total (underlying X) (append P S U).dest ⥤ C} {Z : Total (underlying X) (append P S V).dest ⥤ D}
theorem outerJoin [W.IsIso] [J.IsIso] (w : stage (S := S) (underlying X) U ⋙ J = W) (z : stage (S := S) (underlying X) V ⋙ K = Z) :
    W.strictInv ⋙ wr (S := S) (underlying X) r ⋙ Z = J.strictInv ⋙ restrict (LY (S := S) (underlying X)) U.dest V.dest r.grade r.leg ⋙ K :=
  joinOf w z (functorRigid (stageComparison (S := S) (underlying X) r) (stagePure (S := S) (underlying X) r))
end Span
variable (m : ContextadTotal.Native S)
def wideTotal :=
  letI : (chart S X 4).IsIso := BlockEvaluation.globalIso S (underlying X) 4
  letI : (chart S (obj S 1 X) 3).IsIso := BlockEvaluation.globalIso S (underlying (obj S 1 X)) 3
  (outerJoin S X (U := power S 3) (V := power S 2) (firstTwo m) (resolve3 S X) (resolve2 (S := S) X)).trans (outerM S (obj S 1 X) m)
def wideRead := encodedOfTotal S X (i := 4) (j := 3) (M S (obj S 2 X) m) (wide (tensor m)) (wideTotal S X m).symm
theorem serialRead {i j k} (a : obj S i X ⟶ obj S j X) (b : obj S j X ⟶ obj S k X) (r : Map S i j) (s : Map S j k)
    (p : encode S a = raw X r) (q : encode S b = raw X s) : encode S (a ≫ b) = raw X (comp r s) := by
  apply Eq.trans _ ((congrArg₂ (· ⋙ ·) p q).trans (rawCompose X r s).symm)
  change chart S X i ⋙ tot (a ≫ b) ⋙ (chart S X k).strictInv = _
  rw [totalAfter]
  exact (BlockEvaluation.cancelMiddle _ (tot a) (chart S X j).strictInv (chart S X j) (tot b) _ _ (chart S X j).asIsomorphism.counit_eq rfl).symm
def disjointLeft :=
  serialRead S X (i := 4) (j := 3) (k := 2) (M S (obj S 2 X) m) (K S (M S X m)) (wide (tensor m)) (lastTwo m) (wideRead S X m) (encodedOfTotal S X _ _ (innerM S X m).symm)
def disjointRight :=
  serialRead S X (i := 4) (j := 3) (k := 2) (K S (K S (M S X m))) (M S (obj S 1 X) m) (inside 2 (tensor m)) (firstTwo m) (deepMu S X m) (encodedOfTotal S X _ _ (outerM S X m).symm)
end ContextualComposition.GrothendieckStep.AmbientDisjointFrames
