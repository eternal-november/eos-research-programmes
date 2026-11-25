import Mathlib

namespace SwarmFactory

def secured (finish cut delay deadline : ℤ) (captureEarlier resumes : Bool) : Prop :=
  ((finish < cut ∨ (finish = cut ∧ captureEarlier = true)) ∧ finish ≤ deadline) ∨
    (¬ (finish < cut ∨ (finish = cut ∧ captureEarlier = true)) ∧
       resumes = true ∧ finish + delay ≤ deadline)

theorem exact_launch_threshold (work cut delay deadline launch : ℤ)
    (captureEarlier resumes : Bool) (hdelay : 0 ≤ delay) :
    secured (launch + work) cut delay deadline captureEarlier resumes ↔
      launch ≤ min (cut - (if captureEarlier then 0 else 1)) deadline - work ∨
        (resumes = true ∧ launch ≤ deadline - delay - work) := by
  unfold secured
  cases captureEarlier <;> cases resumes <;> simp <;> omega

theorem completed_before_cut_can_be_lost (processing capture cut delay deadline : ℤ)
    (h₁ : processing < cut) (h₂ : cut ≤ capture) :
    processing < capture ∧ ¬ secured capture cut delay deadline false false := by
  refine ⟨lt_of_lt_of_le h₁ h₂, ?_⟩
  unfold secured
  simp
  omega

theorem equal_time_precedence (cut delay deadline : ℤ) (hc : cut ≤ deadline) :
    secured cut cut delay deadline true false ∧ ¬ secured cut cut delay deadline false false := by
  unfold secured
  simp [hc]

inductive Order where | p | q deriving DecidableEq

def requiredFirst : Bool → Order
  | true => .q
  | false => .p

theorem coarsened_view_has_no_joint_selector :
    ¬ ∃ (k : Order), k = requiredFirst true ∧ k = requiredFirst false := by
  rintro ⟨k,h1,h2⟩
  cases k <;> simp [requiredFirst] at h1 h2

#print axioms exact_launch_threshold
#print axioms completed_before_cut_can_be_lost
#print axioms equal_time_precedence
#print axioms coarsened_view_has_no_joint_selector
end SwarmFactory
