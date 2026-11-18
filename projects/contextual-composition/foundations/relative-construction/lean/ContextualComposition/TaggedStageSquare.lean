module
public import ContextualComposition.TaggedTripleFaces
@[expose] public section
namespace ContextualComposition.GrothendieckStep.TaggedTripleFaces
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks NativeBlocks.Nested NativePacked TripleBoundary MovingCoordinates MovingCell ProjectedCharts FibreEndpoints WholeEvaluator
section
variable {A B C D E : Type*} [Category* A] [Category* B] [Category* C] [Category* D] [Category* E]
theorem stageCongr (p : A ⥤ B) (q : B ⥤ D) (r : A ⥤ C) (s : C ⥤ D) (k : D ⥤ E) (h : p ⋙ q = r ⋙ s) :
    p ⋙ q ⋙ k = r ⋙ s ⋙ k := by rw [← Functor.assoc,h,Functor.assoc]
end
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split) (Y : WordTrace.Pr (B := B))
noncomputable abbrev binaryStages := lastOne (U S) (U S) Y (one S Y) (evaluate S Y) (WholeEvaluator.over S Y) ⋙ evaluate S (one S Y)
theorem binaryOver : binaryStages S Y ⋙ proj S Y = base S Y :=
  tailOver (U S) (U S) Y (one S Y) (ChartRealization.twice S Y) (evaluate S Y) (WholeEvaluator.over S Y) (evaluate S (one S Y)) (WholeEvaluator.over S (one S Y))
noncomputable abbrev ordinaryLeft := dropLast S Y ⋙ binaryStages S (one S Y)
noncomputable abbrev ordinaryRight := regrouping S Y ⋙ foldUnder S Y (binaryStages S Y) (binaryOver S Y) ⋙ outer S Y
theorem ordinary : ordinaryLeft S Y = ordinaryRight S Y :=
  stageCongr (dropLast S Y) (TripleBoundary.mid (U S) (U S) (one S Y) (ChartRealization.twice S Y) (evaluate S (one S Y)) (WholeEvaluator.over S (one S Y))) (regrouping S Y) (foldUnder S Y (binaryStages S Y) (binaryOver S Y)) (outer S Y) (TripleBoundary.associativity (U S) (U S) (U S) Y (one S Y) (ChartRealization.twice S Y)
    (evaluate S Y) (WholeEvaluator.over S Y) (evaluate S (one S Y)) (WholeEvaluator.over S (one S Y)))
end ContextualComposition.GrothendieckStep.TaggedTripleFaces
