module
public import research.workstream_C2.lean.RelationInterface
@[expose] public section
open WitnessedDecompositions WitnessedDecompositions.RelationInterface
namespace NegativeReview
def X (_ : Unit) := Unit
def Y (_ : Unit) := Bool
def a : Interface Unit X := ⟨()⟩
def f (_ : Unit) (_ : Bool) : Unit := ()
example : evaluate ((restrictionQuiver f).mapPath (Quiver.Path.nil : Quiver.Path a a)) =
    (restrictionQuiver f).map (evaluate (Quiver.Path.nil : Quiver.Path a a)) := by
  exact restriction_nonempty_eq_of_surjective f (Quiver.Path.nil : Quiver.Path a a)
    (diagonal a) (by intro i; cases i)
end NegativeReview
