module
public import ContextualComposition.ProjectedCharts
public import ContextualComposition.ChartTotalCell
public import ContextualComposition.FibreReader
@[expose] public section
namespace ContextualComposition.GrothendieckStep.FibreEndpoints
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks NativePacked PackedCuts BlockEvaluation CutCompositor NativeCleavage ChartRealization MovingCoordinates MovingCell ProjectedCharts FibreReader
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split) (Y : WordTrace.Pr (B := B))
theorem rightCast (x : X S Y) : IsTransport ((MovingCell.right S Y x).inv) := by
  rw [rInv]
  exact trans ⟨_,rfl⟩ (castMap _ _)
theorem rightRef : rightTotal S Y = R S Y :=
  (strict (gauge (R S Y) (MovingCell.right S Y)).symm (rightCast S Y)).symm
variable (a : B)
abbrev eff := FibreValue.incl (twice S Y) a
theorem packedR : pick S Y a ⋙ Sigma.desc (refR S Y) = (packedEquiv S Y a).functor ⋙ eff S Y a := by
  have h : pick S Y a ⋙ Sigma.desc (refR S Y) = ZeroPower.Sum.map (second S Y a) ⋙ (packing S Y a).functor ⋙ eff S Y a := by
    apply PackedFree.sigma_ext; intro i
    exact (ChartTotalCell.secondIncl S Y a i).symm
  exact h.trans (congrArg (· ⋙ eff S Y a) (oldChart S Y a))
noncomputable abbrev oldR := off S Y a ⋙ previous S Y a ⋙ eff S Y a
noncomputable abbrev oldL := off S Y a ⋙ stages S Y a ⋙ eff S Y a
theorem rightRestrict : inp S Y a ⋙ rightTotal S Y = oldR S Y a :=
  (congrArg (inp S Y a ⋙ ·) (rightRef S Y)).trans ((congrArg (· ⋙ Sigma.desc (refR S Y)) (reader S Y a)).trans
    (congrArg (fun F => off S Y a ⋙ (N S Y a).inverse ⋙ F) (packedR S Y a)))
end ContextualComposition.GrothendieckStep.FibreEndpoints
