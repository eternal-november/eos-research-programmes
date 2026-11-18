module
public import ContextualComposition.TaggedStageSquare
@[expose] public section
namespace ContextualComposition.GrothendieckStep.TaggedTripleFaces
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks NativePacked MovingCoordinates MovingCell ProjectedCharts FibreEndpoints ChartRealization WholeEvaluator
section
variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
def glue (K : C ⥤ D) (R : D ⥤ C) (k : R ⋙ K ≅ 𝟭 D) (F : D ⥤ E) (T : C ⥤ E) (b : K ⋙ F = T) :
    R ⋙ T ≅ F := eqToIso (congrArg (R ⋙ ·) b.symm) ≪≫ isoWhiskerRight k F
end
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split) (Y : WordTrace.Pr (B := B))
abbrev CutRead (i : Nat × Nat) := Lift.total (Lift.comp (cut S i) (NativePacked.tagged S i)) Y ⋙ binaryStages S Y = refL S Y i
theorem allRead (h : ∀ i, CutRead S Y i) : (MovingCoordinates.chart S Y).functor ⋙ binaryStages S Y = Sigma.desc (refL S Y) := by
  apply PackedFree.sigma_ext; intro i
  exact (congrArg (· ⋙ binaryStages S Y) (chartAt S Y i)).trans (h i)
noncomputable def stageBridge (h : ∀ i, CutRead S Y i) :=
  (gauge (MovingCell.L S Y) (MovingCell.left S Y)) ≪≫
    glue (MovingCoordinates.chart S Y).functor (read S Y) (recover S Y) (binaryStages S Y) (Sigma.desc (refL S Y)) (allRead S Y h)
end ContextualComposition.GrothendieckStep.TaggedTripleFaces
