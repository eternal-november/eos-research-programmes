import Lean

namespace DeferredPlacement

universe u
variable {Bay : Type u}

def Chosen (blocked needed chosen : Bay) : Prop :=
  chosen ≠ blocked ∧ chosen ≠ needed

theorem no_fixed_against_all (blocked fixed : Bay)
    (wonder : ∀ needed, needed ≠ blocked → Chosen blocked needed fixed)
    (openFixed : fixed ≠ blocked) : False :=
  (wonder fixed openFixed).2 rfl

theorem two_branches_iff (read moves t₁ t₂ deadline : Nat) :
    (read + moves + 1 + t₁ ≤ deadline ∧ read + moves + 1 + t₂ ≤ deadline) ↔
    read + moves + 1 + max t₁ t₂ ≤ deadline := by
  omega

/-- At the latest feasible cut, only the current heading can take the bay. -/
theorem no_common_last_heading (read moves t₁ t₂ : Nat)
    (distinct : t₁ > 0 ∨ t₂ > 0) :
    ¬(read + moves + 1 + t₁ ≤ read + moves + 1 ∧
       read + moves + 1 + t₂ ≤ read + moves + 1) := by
  omega

inductive FirstHeading where | east | north | south deriving DecidableEq

def turnsNorth : FirstHeading → Nat
  | .east => 1 | .north => 0 | .south => 2
def turnsSouth : FirstHeading → Nat
  | .east => 1 | .north => 2 | .south => 0

/-- If east storage is blocked, turning to either remaining bay before a
tick-one reveal erases one branch. Waiting keeps both continuations. -/
theorem preserve_both_early (h : FirstHeading) :
    (1 + 2 + 1 + turnsNorth h ≤ 5 ∧ 1 + 2 + 1 + turnsSouth h ≤ 5) ↔
    h = .east := by
  cases h <;> decide

theorem after_two_prepared (turns : Nat) :
    (2 + 2 + 1 + turns ≤ 5) ↔ turns = 0 := by omega

#print axioms no_fixed_against_all
#print axioms two_branches_iff
#print axioms no_common_last_heading
#print axioms preserve_both_early
#print axioms after_two_prepared
end DeferredPlacement
