import JointArrayLifting
import GraphCoefficientBridge
import Mathlib.Algebra.Group.Prod

namespace BackboneBoundaryTests
open JointArrayLifting

/-- A concrete surjective homomorphism that destroys the zero-cut test. -/
def forgetSecond : (Nat × Nat) →* Nat where
  toFun := Prod.fst
  map_one' := rfl
  map_mul' := fun _ _ => rfl

theorem forgetSecond_surjective : Function.Surjective forgetSecond := by
  intro n; exact ⟨(n,1),rfl⟩

theorem forgetSecond_not_full : ¬FullFiniteLifting forgetSecond := by
  intro hf
  have h := identity_reflection forgetSecond hf (x := (1,0)) rfl
  have h' := congrArg Prod.snd h
  change (0 : Nat) = 1 at h'
  exact Nat.zero_ne_one h'

/-- In the actual graph syntax, inactive source positions must not be supplied
with a synthetic unit equation: the path may carry an active ancestor label. -/
theorem cannot_unit_complete_inactive_leaf :
    JointArrayLifting.eval WitnessedDecompositions.GraphCut.emptyExampleLabels
      (WitnessedDecompositions.GraphCut.nestedEmpty.leafPath
        WitnessedDecompositions.GraphCut.retainedEmpty) ≠ 1 := by
  rw [WitnessedDecompositions.GraphCut.retained_empty_path_not_unit]
  decide

end BackboneBoundaryTests
