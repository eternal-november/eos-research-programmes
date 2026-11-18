module
public import ContextualComposition.ParallelBaseWitness
public import ContextualComposition.ProjectedCharts
@[expose] public section
open CategoryTheory CategoryTheory.Functor
open ContextualComposition.GrothendieckStep
namespace ParallelBaseWitness
open ProjectedCharts MovingCell
theorem leftAmount (k : Nat) : ((proj S Y).map ((leftTotal S Y).map (f k)) : Nat) = k :=
  (weight (leftOver S Y) (f k)).trans (baseWeight k)
theorem rightAmount (k : Nat) : ((proj S Y).map ((rightTotal S Y).map (f k)) : Nat) = k :=
  (weight (rightOver S Y) (f k)).trans (baseWeight k)
example : (leftTotal S Y).map (f 1) ≠ (leftTotal S Y).map (f 2) := by
  intro h
  exact (by decide : (1:Nat) ≠ 2) ((leftAmount 1).symm.trans ((congrArg (proj S Y).map h).trans (leftAmount 2)))
example : (rightTotal S Y).map (f 1) ≠ (rightTotal S Y).map (f 2) := by
  intro h
  exact (by decide : (1:Nat) ≠ 2) ((rightAmount 1).symm.trans ((congrArg (proj S Y).map h).trans (rightAmount 2)))
end ParallelBaseWitness
