import Mathlib

namespace JointAdmission

/-- A qualified settlement excludes a world in which this effect is pending.
    Silence and a nonmatching receipt do not. -/
def Compatible (qualified pending : Bool) : Prop :=
  qualified = true → pending = false

/-- Three uses of one inclusive capacity window. A still owed operation
    may require the backup. A positive receipt discharges only that debt. -/
def Fits (cap used extra retry : Nat) (pending : Bool) : Prop :=
  used + extra + (if pending then retry else 0) ≤ cap

theorem robust_capacity (cap used extra retry : Nat) (qualified : Bool) :
    (∀ pending, Compatible qualified pending → Fits cap used extra retry pending) ↔
      (used + extra + (if qualified then 0 else retry) ≤ cap) := by
  cases qualified
  · constructor
    · intro h
      exact h true (by simp [Compatible])
    · intro h pending _
      cases pending <;> simp [Fits] at *
      · omega
      · exact h
  · constructor
    · intro h
      exact h false (by simp [Compatible])
    · intro h pending hp
      have e : pending = false := hp rfl
      subst pending
      simpa [Fits] using h

theorem disjoint_local_checks_not_joint (cap used extra retry : Nat)
    (hx : used + extra ≤ cap) (hr : used + retry ≤ cap)
    (hjoint : cap < used + extra + retry) :
    Fits cap used extra retry false ∧ Fits cap used 0 retry true ∧
      ¬ (∀ pending, Compatible false pending → Fits cap used extra retry pending) := by
  refine ⟨by simpa [Fits] using hx, by simpa [Fits] using hr, ?_⟩
  rw [robust_capacity]
  simp
  omega

theorem fixture (qualified : Bool) :
    (∀ pending, Compatible qualified pending → Fits 5 0 3 3 pending) ↔
      qualified = true := by
  rw [robust_capacity]
  cases qualified <;> decide

end JointAdmission

#print axioms JointAdmission.robust_capacity
#print axioms JointAdmission.disjoint_local_checks_not_joint
#print axioms JointAdmission.fixture
