module
public import ContextualComposition.RepresentableComparisonEquivalences
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableComparisonBinaryPin
open CategoryTheory
open RepresentableBicategoryAssembly
open scoped CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
universe u v w
variable {B : Type u} {H : B → B → Type v} [∀ x y, Category.{w} (H x y)]
variable (O : Operations H) (L : Laws O)
theorem binary (x y z : B) :
    @RepresentableComparisonEquivalences.binary B (build O L) x y z = O.multiply (x := x) (y := y) (z := z) := by
  refine Functor.hext (F := @RepresentableComparisonEquivalences.binary B (build O L) x y z)
    (G := O.multiply (x := x) (y := y) (z := z)) (fun _ => rfl) ?_
  rintro ⟨f,g⟩ ⟨f',g'⟩ ⟨r,s⟩
  apply heq_of_eq
  change compCell O r (𝟙 g) ≫ compCell O (𝟙 f') s = compCell O r s
  rw [←cellComp,Category.comp_id,Category.id_comp]
end ContextualComposition.GrothendieckStep.RepresentableComparisonBinaryPin
