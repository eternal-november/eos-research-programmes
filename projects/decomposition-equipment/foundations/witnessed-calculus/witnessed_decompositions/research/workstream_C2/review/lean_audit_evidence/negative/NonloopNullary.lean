module
public import research.workstream_C2.lean.RelationInterface
@[expose] public section
open WitnessedDecompositions WitnessedDecompositions.RelationInterface
namespace NegativeReview
def X (_ : Bool) := Unit
def a : Interface Bool X := ⟨false⟩
def b : Interface Bool X := ⟨true⟩
def bad : Quiver.Path a b := Quiver.Path.nil
end NegativeReview
