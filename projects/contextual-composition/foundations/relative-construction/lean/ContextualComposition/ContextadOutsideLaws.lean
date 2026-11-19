module
public import ContextualComposition.ContextadOuterCharts
public import ContextualComposition.ContextadOuterRecognition
public import ContextualComposition.ContextadChartDescent
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadOuterCharts
open CategoryTheory CategoryTheory.Functor Opposite NativeBlocks SpanApex NativeCleavage BoundaryPaste
open ContextadRoutes ContextadLawTransport ContextadNativeLaws ContextadChartDescent FibreValue
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (Y : PackedCuts.Psh.{u,max u v,u,v} B)
noncomputable def outerUnitTotal (d : ContextadUnit.Data P) : global Y (suffix (insert S d)) ≅ global (LY (S := S) Y) (insert S d) := by
  letI : (BlockEvaluation.global S Y (0+1)).IsIso := BlockEvaluation.globalIso S Y (0+1)
  letI : (BlockEvaluation.global S (LY (S := S) Y) 0).IsIso := BlockEvaluation.globalIso S (LY (S := S) Y) 0
  exact chartIso (stage (S := S) Y (power S 0)) (stage (S := S) Y (power S 1))
      (BlockEvaluation.global S Y (0+1)) (BlockEvaluation.global S Y (1+1))
      (BlockEvaluation.global S (LY (S := S) Y) 0) (BlockEvaluation.global S (LY (S := S) Y) 1)
      (raw Y (suffix (insert S d))) (raw (LY (S := S) Y) (insert S d))
      (resolve0 (S := S) Y) (resolve1 (S := S) Y) (stageComparison (S := S) Y (insert S d))
theorem outerUnitPure (d : ContextadUnit.Data P) (x) : Pure ((proj (PackedFree.pow S Y 2)).map ((outerUnitTotal Y d).hom.app x)) := by
  let _ : (BlockEvaluation.global S Y (0+1)).IsIso := BlockEvaluation.globalIso S Y (0+1)
  let _ : (BlockEvaluation.global S (LY (S := S) Y) 0).IsIso := BlockEvaluation.globalIso S (LY (S := S) Y) 0
  apply chartPure (stage (S := S) Y (power S 0)) (stage (S := S) Y (power S 1))
      (BlockEvaluation.global S Y (0+1)) (BlockEvaluation.global S Y (1+1))
      (BlockEvaluation.global S (LY (S := S) Y) 0) (BlockEvaluation.global S (LY (S := S) Y) 1)
      (raw Y (suffix (insert S d))) (raw (LY (S := S) Y) (insert S d))
      (resolve0 (S := S) Y) (resolve1 (S := S) Y) (stageComparison (S := S) Y (insert S d))
  intro z
  rw [BlockEvaluation.globalOver]
  exact pureMap (power S 1).source (stageVertical (S := S) Y (insert S d) z)
noncomputable def outerUnit (d : ContextadUnit.Data P) (A : B) : evaluate Y (suffix (insert S d)) A ≅ ContextadUnit.atBase d (LY (S := S) Y) A :=
  localIso (global Y (suffix (insert S d))) (global (LY (S := S) Y) (insert S d)) (over Y _) (over _ _)
    (outerUnitTotal Y d) (outerUnitPure Y d) A ≪≫ eqToIso (evalUnit d (LY (S := S) Y) A)
noncomputable def outerTensorTotal (m : ContextadTotal.Native S) : global Y (suffix (tensor m)) ≅ global (LY (S := S) Y) (tensor m) := by
  letI : (BlockEvaluation.global S Y (2+1)).IsIso := BlockEvaluation.globalIso S Y (2+1)
  letI : (BlockEvaluation.global S (LY (S := S) Y) 2).IsIso := BlockEvaluation.globalIso S (LY (S := S) Y) 2
  exact chartIso (stage (S := S) Y (power S 2)) (stage (S := S) Y (power S 1))
      (BlockEvaluation.global S Y (2+1)) (BlockEvaluation.global S Y (1+1))
      (BlockEvaluation.global S (LY (S := S) Y) 2) (BlockEvaluation.global S (LY (S := S) Y) 1)
      (raw Y (suffix (tensor m))) (raw (LY (S := S) Y) (tensor m))
      (resolve2 (S := S) Y) (resolve1 (S := S) Y) (stageComparison (S := S) Y (tensor m))
theorem outerTensorPure (m : ContextadTotal.Native S) (x) : Pure ((proj (PackedFree.pow S Y 2)).map ((outerTensorTotal Y m).hom.app x)) := by
  let _ : (BlockEvaluation.global S Y (2+1)).IsIso := BlockEvaluation.globalIso S Y (2+1)
  let _ : (BlockEvaluation.global S (LY (S := S) Y) 2).IsIso := BlockEvaluation.globalIso S (LY (S := S) Y) 2
  apply chartPure (stage (S := S) Y (power S 2)) (stage (S := S) Y (power S 1))
      (BlockEvaluation.global S Y (2+1)) (BlockEvaluation.global S Y (1+1))
      (BlockEvaluation.global S (LY (S := S) Y) 2) (BlockEvaluation.global S (LY (S := S) Y) 1)
      (raw Y (suffix (tensor m))) (raw (LY (S := S) Y) (tensor m))
      (resolve2 (S := S) Y) (resolve1 (S := S) Y) (stageComparison (S := S) Y (tensor m))
  intro z
  rw [BlockEvaluation.globalOver]
  exact pureMap (power S 1).source (stageVertical (S := S) Y (tensor m) z)
noncomputable def outerTensor (m : ContextadTotal.Native S) (A : B) : evaluate Y (suffix (tensor m)) A ≅ ContextadCoherence.actual m (LY (S := S) Y) A :=
  localIso (global Y (suffix (tensor m))) (global (LY (S := S) Y) (tensor m)) (over Y _) (over _ _)
    (outerTensorTotal Y m) (outerTensorPure Y m) A ≪≫ eqToIso (evalTensor (LY (S := S) Y) m A)
end ContextualComposition.GrothendieckStep.ContextadOuterCharts
