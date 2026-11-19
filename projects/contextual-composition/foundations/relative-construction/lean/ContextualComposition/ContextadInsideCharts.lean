module
public import ContextualComposition.ContextadWeakAction
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadWeakAction
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks NativePacked
open ContextadRoutes ContextadLawTransport ContextadNativeLaws
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
section General
variable {C₀ C₁ C₂ D₀ D₁ D₂ V W : Type*}
  [Category* C₀] [Category* C₁] [Category* C₂] [Category* D₀] [Category* D₁] [Category* D₂] [Category* V] [Category* W]
theorem changeCharts (p : C₀ ⥤ C₁) (q : D₀ ⥤ D₁) (U : C₀ ⥤ C₂) (V' : D₀ ⥤ D₂)
    (J : C₁ ⥤ C₂) (K : D₁ ⥤ D₂) [U.IsIso] [J.IsIso]
    (r : C₀ ⥤ D₀) (t : C₁ ⥤ D₁) (s : V ⥤ W) (i : V ⥤ C₁) (j : W ⥤ D₁)
    (x : V ⥤ C₂) (y : W ⥤ D₂)
    (a : p ⋙ J = U) (b : q ⋙ K = V') (c : r ⋙ q = p ⋙ t) (d : s ⋙ j = i ⋙ t)
    (h : i ⋙ J = x) (k : j ⋙ K = y) :
    x ⋙ (U.strictInv ⋙ r ⋙ V') = s ⋙ y := by
  have n : U.strictInv ⋙ r ⋙ V' = J.strictInv ⋙ t ⋙ K := by
    apply U.asIsomorphism.functor_comp_injective
    refine (ContextadRecognition.eraseInv U _).trans ?_
    refine (congrArg (r ⋙ ·) b.symm).trans ?_
    refine (congrArg (· ⋙ K) c).trans ?_
    refine Eq.trans ?_ (congrArg (· ⋙ J.strictInv ⋙ t ⋙ K) a)
    exact (congrArg (p ⋙ ·) (ContextadRecognition.eraseInv J (t ⋙ K))).symm
  exact (congrArg (x ⋙ ·) n).trans ((congrArg (· ⋙ J.strictInv ⋙ t ⋙ K) h.symm).trans
    ((congrArg (i ⋙ ·) (ContextadRecognition.eraseInv J (t ⋙ K))).trans
      ((congrArg (· ⋙ K) d.symm).trans (congrArg (s ⋙ ·) k))))
end General
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (Y : PackedCuts.Psh.{u,max u v,u,v} B)
theorem selfTransport {C : Type*} [Category* C] {G : PackedCuts.Psh.{u,max u v,u,v} B}
    (F : C ⥤ Total G (𝟭 B)) (h : G = G) : F ⋙ BlockCompositor.transport h = F :=
  Functor.comp_id F
theorem splitTransport (k i : Nat) : splitAt (S := S) Y k i ⋙ BlockEvaluation.global S (PackedFree.pow S Y i) k =
    BlockEvaluation.global S Y (k+i) ⋙ BlockCompositor.transport (PackedCuts.sameLength S Y (k,i)).symm :=
  BlockCompositor.total S Y k i
theorem splitOne0 : splitAt (S := S) Y 1 0 ⋙ BlockEvaluation.global S (PackedFree.pow S Y 0) 1 = BlockEvaluation.global S Y 1 :=
  (splitTransport (S := S) Y 1 0).trans (selfTransport (G := PackedFree.pow S Y (1+0)) (BlockEvaluation.global S Y (1+0)) (PackedCuts.sameLength S Y (1,0)).symm)
theorem splitOne1 : splitAt (S := S) Y 1 1 ⋙ BlockEvaluation.global S (PackedFree.pow S Y 1) 1 = BlockEvaluation.global S Y 2 :=
  (splitTransport (S := S) Y 1 1).trans (selfTransport (G := PackedFree.pow S Y (1+1)) (BlockEvaluation.global S Y (1+1)) (PackedCuts.sameLength S Y (1,1)).symm)
theorem splitOne2 : splitAt (S := S) Y 1 2 ⋙ BlockEvaluation.global S (PackedFree.pow S Y 2) 1 = BlockEvaluation.global S Y 3 :=
  (splitTransport (S := S) Y 1 2).trans (selfTransport (G := PackedFree.pow S Y (1+2)) (BlockEvaluation.global S Y (1+2)) (PackedCuts.sameLength S Y (1,2)).symm)
theorem insideUnit (d : ContextadUnit.Data P) (A : B) :
    evaluate Y (inside 1 (insert S d)) A = action (P.extend A) (global Y (insert S d)) (over Y (insert S d)) := by
  apply ContextadFinal.cancelIncl (PackedFree.pow S Y 2) A
  refine (evalIncl Y _ A).trans ?_
  exact changeCharts (splitAt Y 1 0) (splitAt Y 1 1) (BlockEvaluation.global S Y 1) (BlockEvaluation.global S Y 2)
    (BlockEvaluation.global S (PackedFree.pow S Y 0) 1) (BlockEvaluation.global S (PackedFree.pow S Y 1) 1)
    (raw Y (inside 1 (insert S d))) _ _ (ContextadVertical.insertOne (S := S) A (PackedFree.pow S Y 0))
    (ContextadVertical.insertOne (S := S) A (PackedFree.pow S Y 1)) _ _
    (splitOne0 Y) (splitOne1 Y) (splitInside Y 1 (insert S d)) (unaryChange (S := S) A _ _)
    (ContextadUnary.recognition S A _) (ContextadUnary.recognition S A _)
theorem insideTensor (m : ContextadTotal.Native S) (A : B) :
    evaluate Y (inside 1 (tensor m)) A = action (P.extend A) (global Y (tensor m)) (over Y (tensor m)) := by
  apply ContextadFinal.cancelIncl (PackedFree.pow S Y 2) A
  refine (evalIncl Y _ A).trans ?_
  exact changeCharts (splitAt Y 1 2) (splitAt Y 1 1) (BlockEvaluation.global S Y 3) (BlockEvaluation.global S Y 2)
    (BlockEvaluation.global S (PackedFree.pow S Y 2) 1) (BlockEvaluation.global S (PackedFree.pow S Y 1) 1)
    (raw Y (inside 1 (tensor m))) _ _ (ContextadVertical.insertOne (S := S) A (PackedFree.pow S Y 2))
    (ContextadVertical.insertOne (S := S) A (PackedFree.pow S Y 1)) _ _
    (splitOne2 Y) (splitOne1 Y) (splitInside Y 1 (tensor m)) (unaryChange (S := S) A _ _)
    (ContextadUnary.recognition S A _) (ContextadUnary.recognition S A _)
end ContextualComposition.GrothendieckStep.ContextadWeakAction
