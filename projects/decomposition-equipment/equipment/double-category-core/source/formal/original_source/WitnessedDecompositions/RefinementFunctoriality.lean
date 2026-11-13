module

public import WitnessedDecompositions.SemanticRefinement
public import Mathlib.CategoryTheory.EqToHom

/-! Literal identity/composition compatibility for semantic refinement functors. -/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v w w' w''
namespace WitnessedDecompositions.SemanticRefinement
open CategoryTheory
variable {V : Type u} [Quiver.{v} V]
variable {M : Calc.{u,v,w} V} {N : Calc.{u,v,w'} V} {P : Calc.{u,v,w''} V}

@[simp] theorem functor_identity (M : Calc.{u,v,w} V) (c : Component V) :
    functor (Calc.Hom.id M) c = 𝟭 (Object M c) := by
  rfl

@[simp] theorem functor_composite (H : Calc.Hom M N) (K : Calc.Hom N P)
    (c : Component V) : functor (H.comp K) c = functor H c ⋙ functor K c := by
  refine CategoryTheory.Functor.ext (F := functor (H.comp K) c)
    (G := functor H c ⋙ functor K c) (fun _ => rfl) ?_
  intro a b f
  simp only [CategoryTheory.eqToHom_refl, CategoryTheory.Category.id_comp,
    CategoryTheory.Category.comp_id]
  exact mapArrow_composite H K f

/-- Strict inverse calculus maps yield strictly inverse refinement functors. -/
theorem functor_inverse (H : Calc.Hom M N) (K : Calc.Hom N M)
    (hHK : H.comp K = Calc.Hom.id M) (hKH : K.comp H = Calc.Hom.id N)
    (c : Component V) :
    functor H c ⋙ functor K c = 𝟭 (Object M c) ∧
      functor K c ⋙ functor H c = 𝟭 (Object N c) := by
  constructor
  · rw [← functor_composite, hHK, functor_identity]
  · rw [← functor_composite, hKH, functor_identity]

end WitnessedDecompositions.SemanticRefinement
