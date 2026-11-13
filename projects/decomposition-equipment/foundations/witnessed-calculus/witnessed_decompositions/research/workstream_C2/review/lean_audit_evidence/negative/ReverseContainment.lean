module
public import research.workstream_C2.lean.RelationInterface
@[expose] public section
open WitnessedDecompositions WitnessedDecompositions.RelationInterface
namespace NegativeReview
def X (_ : Unit) := Unit
def a : Interface Unit X := ⟨()⟩
def top : Rel a a := fun _ _ => True
def bad : ContainmentOp (⟨a,a,fun _ _ => False⟩ : Component (Interface Unit X)) :=
  ⟨top.toPath, by intro x y h; exact h⟩
end NegativeReview
