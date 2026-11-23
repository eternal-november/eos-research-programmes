module
public import ContextualComposition.RelativeTensorCocones
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

@[expose] public section
namespace ContextualComposition.RelativeTensor
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false

section
universe v u vF uF vG uG
variable {B : Type u} [Category.{v} B] (F : LocallyDiscrete B ⥤ᵖ Cat.{vF,uF}) (G : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vG,uG})

/-- A native arrow can acquire an inverse when the covariant action sends it to an isomorphism. This follows from balance naturality without declaring a native generator invertible. -/
theorem native_iso_of_action {i j : B} (u : i ⟶ j) {x x' : F.obj ⟨i⟩} (a : x ⟶ x') (y : G.obj ⟨op j⟩)
    [IsIso ((forward F u).map a)] : IsIso ((insertion F G i).map (productMap a (𝟙 ((backward G u).obj y)))) := by
  let t := (insertion F G j).mapIso ((asIso ((forward F u).map a)).prod (Iso.refl y))
  let s := balancing F G u x y ≪≫ t ≪≫ (balancing F G u x' y).symm
  have h := (restrict (𝟭 (Tensor F G))).natural u a (𝟙 y)
  change (insertion F G i).map (productMap a ((backward G u).map (𝟙 y))) ≫ (balancing F G u x' y).hom =
    (balancing F G u x y).hom ≫ t.hom at h
  rw [Functor.map_id] at h
  have he : (insertion F G i).map (productMap a (𝟙 ((backward G u).obj y))) = s.hom := by
    apply (cancel_mono (balancing F G u x' y).hom).mp
    change _ = ((balancing F G u x y).hom ≫ t.hom ≫ (balancing F G u x' y).inv) ≫ _
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact h
  rw [he]
  infer_instance
end

namespace Collapse
open WalkingParallelPair WalkingParallelPairHom
abbrev One := Discrete PUnit.{1}
abbrev star : One := ⟨⟨⟩⟩
abbrev collapse : WalkingParallelPair ⥤ One := (Functor.const _).obj star
/-- The parallel-pair base supplies a transition from the native category to the terminal category. Both parallel transitions act by the same constant functor. -/
abbrev firstAction := (parallelPair collapse.toCatHom collapse.toCatHom).toPseudofunctor'
abbrev secondAction := ((Functor.const WalkingParallelPairᵒᵖ).obj (Cat.of One)).toPseudofunctor'

theorem source_noniso : ¬ IsIso (C := WalkingParallelPair) (X := zero) (Y := one) left := by
  intro h
  have k : WalkingParallelPairHom one zero := inv (C := WalkingParallelPair) (X := zero) (Y := one) left
  cases k

theorem product_noniso : ¬ IsIso (C := WalkingParallelPair × One)
    (productMap (left : zero ⟶ one) (𝟙 star)) := by
  intro h
  exact source_noniso ((CategoryTheory.Prod.fst WalkingParallelPair One).map_isIso (productMap (left : zero ⟶ one) (𝟙 star)))

theorem inserted_iso :
    IsIso ((insertion firstAction secondAction zero).map
      (productMap (left : zero ⟶ one) (𝟙 ((backward secondAction left).obj star)))) := by
  have : IsIso ((forward firstAction left).map (left : zero ⟶ one)) := by
    change IsIso (𝟙 star)
    infer_instance
  exact native_iso_of_action firstAction secondAction left left star

end Collapse
end ContextualComposition.RelativeTensor
