module

public import ContextualComposition.ConeWiring
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Opposite

/-! Simultaneous representability in every finite arity, with the resulting coherent tensor on the opposite unary category. -/

@[expose] public section
namespace ContextualComposition.ConeRepresentability

open CategoryTheory CategoryTheory.Limits ConeWiring Opposite
universe u v
variable (C : Type u) [Category.{v} C]

theorem finite_iff : (∀ n (P : Fin n → C), ∃ R : C, Nonempty (Represents R P)) ↔ HasFiniteProducts C := by
  constructor
  · intro hr
    refine ⟨fun n => ⟨fun D => ?_⟩⟩
    let := (representable_iff_product (D.obj ∘ Discrete.mk)).mp (hr n _)
    exact hasLimit_of_iso (Discrete.natIsoFunctor (F := D)).symm
  · intro h n P
    let := h
    exact (representable_iff_product P).mpr inferInstance

noncomputable abbrev unaryMonoidal [HasFiniteProducts C] : MonoidalCategory Cᵒᵖ :=
  letI : CartesianMonoidalCategory C := CartesianMonoidalCategory.ofHasFiniteProducts
  inferInstance

theorem unary_tensor [HasFiniteProducts C] (X Y : C) :
    letI := unaryMonoidal C
    (MonoidalCategory.tensorObj (op X) (op Y)).unop = (X ⨯ Y) := rfl

theorem unary_unit [HasFiniteProducts C] :
    letI := unaryMonoidal C
    (MonoidalCategory.tensorUnit (C := Cᵒᵖ)).unop = ⊤_ C := rfl

end ContextualComposition.ConeRepresentability
