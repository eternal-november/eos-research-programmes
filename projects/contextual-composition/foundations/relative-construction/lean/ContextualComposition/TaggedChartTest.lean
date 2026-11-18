module
public import ContextualComposition.TaggedFixedSquare
@[expose] public section
namespace ContextualComposition.GrothendieckStep.TaggedChartTest
open CategoryTheory CategoryTheory.Functor Opposite
section General
variable {C : Type*} [Category* C] {A B C₀ D A' B' C' D' : C}
theorem transfer (a : A ⟶ B) (b : C₀ ⟶ D) (s : A ⟶ C₀) (t : B ⟶ D)
    (a' : A' ⟶ B') (b' : C' ⟶ D') (s' : A' ⟶ C') (t' : B' ⟶ D')
    (u : A ⟶ A') (v : B ⟶ B') (w : C₀ ⟶ C') (z : D ⟶ D') [Mono z]
    (ha : a ≫ v = u ≫ a') (hb : b ≫ z = w ≫ b') (hs : s ≫ w = u ≫ s') (ht : t ≫ z = v ≫ t')
    (h : a' ≫ t' = s' ≫ b') : a ≫ t = s ≫ b := by
  apply (cancel_mono z).mp
  calc
    _ = u ≫ a' ≫ t' := by rw [Category.assoc,ht,← Category.assoc,ha,Category.assoc]
    _ = u ≫ s' ≫ b' := congrArg (u ≫ ·) h
    _ = _ := by symm; rw [Category.assoc,hb,← Category.assoc,hs,Category.assoc]
end General
universe u v
open TaggedTripleCover
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split) (Y : WordTrace.Pr (B := B))
variable {D : Type*} [Category* D] {F G : target S Y ⥤ D}
theorem uniqueChart (p q : F ⟶ G) {V : ∀ n m k, TripleTrace.input S Y n m k ⥤ D}
    (v : ∀ n m k, incl S Y n m k ⋙ G ≅ V n m k)
    (h : ∀ n m k, whiskerLeft (incl S Y n m k) p ≫ (v n m k).hom =
      whiskerLeft (incl S Y n m k) q ≫ (v n m k).hom) : p = q :=
  detect S Y p q fun n m k => (cancel_mono (v n m k).hom).mp (h n m k)
end ContextualComposition.GrothendieckStep.TaggedChartTest
