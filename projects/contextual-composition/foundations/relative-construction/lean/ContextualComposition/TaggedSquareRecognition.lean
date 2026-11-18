module
public import ContextualComposition.TaggedChartTest
public import ContextualComposition.TaggedSourceCorner
@[expose] public section
namespace ContextualComposition.GrothendieckStep.TaggedSquareRecognition
open CategoryTheory CategoryTheory.Functor Opposite SpanApex TaggedTripleCover TaggedFixedSquare TaggedTripleFaces TripleEvaluation
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split) (Y : WordTrace.Pr (B := B))
abbrev dst := Total (three S Y) (𝟭 B)
abbrev Face := target S Y ⥤ dst S Y
variable {A B₀ C D : Face S Y}
section
variable (n m k : Nat)
abbrev pull (F : Face S Y) := incl S Y n m k ⋙ F
abbrev edge {F G : Face S Y} (f : F ⟶ G) := whiskerLeft (incl S Y n m k) f
noncomputable abbrev a₀ := stagedLeft S Y n m k ⋙ packOut S Y n m k
noncomputable abbrev b₀ := joinFirst S Y n m k ⋙ packOut S Y n m k
noncomputable abbrev c₀ := stagedRight S Y n m k ⋙ packOut S Y n m k
noncomputable abbrev d₀ := joinLast S Y n m k ⋙ packOut S Y n m k
end
variable (a : A ⟶ B₀) (b : C ⟶ D) (s : A ⟶ C) (t : B₀ ⟶ D)
theorem onCharts
    (u : ∀ n m k, pull S Y n m k A ≅ a₀ S Y n m k)
    (v : ∀ n m k, pull S Y n m k B₀ ≅ b₀ S Y n m k)
    (w : ∀ n m k, pull S Y n m k C ≅ c₀ S Y n m k)
    (z : ∀ n m k, pull S Y n m k D ≅ d₀ S Y n m k)
    (ha : ∀ n m k, edge S Y n m k a ≫ (v n m k).hom = (u n m k).hom ≫ fa S Y n m k)
    (hb : ∀ n m k, edge S Y n m k b ≫ (z n m k).hom = (w n m k).hom ≫ fb S Y n m k)
    (hs : ∀ n m k, edge S Y n m k s ≫ (w n m k).hom = (u n m k).hom ≫ fs S Y n m k)
    (ht : ∀ n m k, edge S Y n m k t ≫ (z n m k).hom = (v n m k).hom ≫ ft S Y n m k) :
    a ≫ t = s ≫ b := by
  apply detect S Y; intro n m k
  exact TaggedChartTest.transfer _ _ _ _ _ _ _ _ _ _ _ _ (ha n m k) (hb n m k) (hs n m k) (ht n m k) (fixed S Y n m k)
end ContextualComposition.GrothendieckStep.TaggedSquareRecognition
