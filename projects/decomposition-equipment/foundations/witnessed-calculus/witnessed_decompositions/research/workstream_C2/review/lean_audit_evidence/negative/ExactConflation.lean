module
public import research.workstream_C2.lean.RelationInterface
@[expose] public section
open WitnessedDecompositions WitnessedDecompositions.RelationInterface
namespace NegativeReview
def X (_ : Unit) := Bool
def a : Interface Unit X := ⟨()⟩
def bad : ExactOp (⟨a,a,fun _ _ => True⟩ : Component (Interface Unit X)) :=
  ⟨(diagonal a).toPath, rfl⟩
end NegativeReview
