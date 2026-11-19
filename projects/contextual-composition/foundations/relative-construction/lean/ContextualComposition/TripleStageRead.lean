module
public import ContextualComposition.NativeRegroupChart
public import ContextualComposition.NativeFoldChart
@[expose] public section
namespace ContextualComposition.GrothendieckStep.TripleStageRead
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks NativeBlocks.Nested NativePacked BlockEvaluation ChartRealization WholeEvaluator TaggedTripleFaces NativeRegroupChart TaggedFixedSquare TripleEvaluation
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split) (Y : WordTrace.Pr (B := B)) (n m k : Nat)
abbrev G := out S (out S Y k) m
abbrev move := ChainPayload.fibreMap (put S Y (m,k)) (power S n).dest
abbrev stageTag := Lift.total (tag (power S) n) (twice S Y)
noncomputable abbrev smallFold := NativeFoldChart.foldAt Y (power S n) (fixed S (m,k)) (totalStages S Y m k) (totalOver S Y m k)
noncomputable abbrev bigFold := foldUnder S Y (binaryStages S Y) (binaryOver S Y)
theorem suffixChart : rightIncl S Y n m k ⋙ bigFold S Y = smallFold S Y n m k ⋙ move S Y n m k ⋙ stageTag S Y n :=
  NativeFoldChart.restriction Y (tag (power S) n) (NativePacked.tagged S (m,k)) (put S Y (m,k)) (totalStages S Y m k) (binaryStages S Y)
    (totalOver S Y m k) (binaryOver S Y) (CutReadout.matched S Y m k)
theorem outerBranch : move S Y n m k ⋙ branch S (twice S Y) n = global S (G S Y m k) n ⋙ packOut S Y n m k :=
  (congrArg (· ⋙ ChainPayload.fibreMap (PackedFree.inc S (twice S Y) n) (𝟭 B)) (CutPayload.globalMap S (put S Y (m,k)) n)).trans
    (congrArg (global S (G S Y m k) n ⋙ ·) (ChainPayload.fibreMap_comp _ _ _).symm)
theorem grouped : rightIncl S Y n m k ⋙ bigFold S Y ⋙ outer S Y = (smallFold S Y n m k ⋙ global S (G S Y m k) n) ⋙ packOut S Y n m k :=
  CutReadout.joinRows (rightIncl S Y n m k) (bigFold S Y) (outer S Y) (smallFold S Y n m k) (move S Y n m k) (stageTag S Y n)
    (branch S (twice S Y) n) (global S (G S Y m k) n) (packOut S Y n m k) (suffixChart S Y n m k) (WholeEvaluator.tagged S (twice S Y) n) (outerBranch S Y n m k)
section Generic
variable {A B C D E F : Type*} [Category* A] [Category* B] [Category* C] [Category* D] [Category* E] [Category* F]
theorem frontJoin (i : A ⥤ B) (j : B ⥤ C) (p : A ⥤ D) (q : D ⥤ C) (u : C ⥤ E) (e : D ⥤ F) (v : F ⥤ E)
    (x : i ⋙ j = p ⋙ q) (y : q ⋙ u = e ⋙ v) : i ⋙ j ⋙ u = (p ⋙ e) ⋙ v := by rw [← Functor.assoc,x,Functor.assoc,y,Functor.assoc]
end Generic
theorem rightStage : TaggedTripleCover.incl S Y n m k ⋙ ordinaryRight S Y = TaggedSquareRecognition.c₀ S Y n m k :=
  frontJoin _ _ _ _ _ _ _ (totalRegroup S Y n m k) (grouped S Y n m k)
theorem leftStage : TaggedTripleCover.incl S Y n m k ⋙ ordinaryLeft S Y = TaggedSquareRecognition.a₀ S Y n m k :=
  (congrArg (TaggedTripleCover.incl S Y n m k ⋙ ·) (ordinary S Y)).trans
    ((rightStage S Y n m k).trans (congrArg (· ⋙ packOut S Y n m k) (stages S Y n m k)).symm)
end ContextualComposition.GrothendieckStep.TripleStageRead
