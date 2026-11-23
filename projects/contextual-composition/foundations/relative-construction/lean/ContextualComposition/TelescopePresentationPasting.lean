module
public import ContextualComposition.TelescopeAmbientMixed
public import ContextualComposition.TelescopeAmbientTag

@[expose] public section
namespace ContextualComposition.GrothendieckStep.TelescopePresentationPasting
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite
open NativeCleavage NativeBlocks SpanApex TelescopeSquares CoproductSpan CoproductSpan.All SumChange
open ContextadAmbientPayload AmbientBicategory TaggedMixed ForwardMixed
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B}
variable (S : P.Split) {X Y : Obj.{u,v} B} (f : X ⟶ Y) {A D : B} (a : A ⟶ D)

theorem leaf_alignment (n : Nat) (x : Total (underlying X) (leg (src S) (dst S) D n)) :
    Aligned ((TelescopeAmbientMixed.nativeLeaf S f a n).hom.app x)
      ((TelescopeAmbientBase.presented f.hom (dst S n) (src S n) (SpanPull.All.parts S n) a).hom.app x) := by
  cases n <;> exact Aligned.refl _

theorem compare_alignment (n : Nat) (x : Total (underlying X) (leg (src S) (dst S) D n)) :
    Aligned ((compare (src S) (dst S) A (underlying Y)).map
      ((TelescopeAmbientMixed.taggedGrid S f a).cell.app ⟨n,x⟩))
      ((TelescopeAmbientMixed.wholeGrid S f a).cell.app
        ((compare (src S) (dst S) D (underlying X)).obj ⟨n,x⟩)) :=
  ((leaf_alignment S f a n x).map (Sigma.incl n ⋙ compare (src S) (dst S) A (underlying Y))).trans
    (TelescopeAmbientTag.compareCell (src S) (dst S) (SpanPull.All.parts S) f.hom a n x)

/-- Reindexing and an arbitrary strong payload map agree across the actual tagged-to-whole comparison. -/
theorem presentation_law : Cube.Law (TelescopeAmbientMixed.presentation S f a).forward := by
  rintro ⟨n,x⟩
  exact IsTransport.hexagon (compare_alignment S f a n x)
    (ForwardMixed.All.comparisonTransport S (underlying Y) a _)
    (IsTransport.map (SpanPull.All.pull S (underlying Y) a)
      (IsTransport.app (TelescopeGradeChange.compare_payload f.hom (src S) (dst S) D).symm ⟨n,x⟩))
    (IsTransport.app (TelescopeGradeChange.compare_payload f.hom (src S) (dst S) A).symm
      ((ZeroPower.Sum.map (leafPull S (underlying X) a)).obj ⟨n,x⟩))
    (IsTransport.map (atEndpoint f.hom (wholeLeg (src S) (dst S) A))
      (ForwardMixed.All.comparisonTransport S (underlying X) a _))

/-- Only the native component cube at each length remains in the mixed evaluation equation. -/
theorem evaluation_of_lengths (law : ∀ n, Cube.Law (TelescopeAmbientMixed.leafMap S f a n)) :
    Commuting (TelescopeAmbientMixed.evaluationCube S f a) :=
  TelescopeAmbientMixed.evaluation_of_faces S f a (presentation_law S f a) law

end ContextualComposition.GrothendieckStep.TelescopePresentationPasting
