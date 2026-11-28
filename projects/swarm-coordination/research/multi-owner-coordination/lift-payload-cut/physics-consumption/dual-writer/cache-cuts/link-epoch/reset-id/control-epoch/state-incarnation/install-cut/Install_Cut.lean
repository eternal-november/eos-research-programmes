import Mathlib
namespace InstallCut

def authorized (life installed request : Nat) : Prop :=
  life = installed ∧ installed = request

theorem no_old_effect {old now installed : Nat} (h : old ≠ now) :
    ¬ authorized now installed old := by
  intro ⟨a,b⟩
  exact h (a.trans b).symm

theorem qualified_install_idempotent {a i c : Nat}
    (h : a = i) : (if c = a then c else i) = i := by
  split <;> omega

theorem monotone_without_life_is_not_sound :
    ∃ old new : Nat, old < new ∧ max old old = old ∧
      ¬ authorized new (max old old) old := by
  exact ⟨0,1,by decide,by decide,by simp [authorized]⟩

theorem service_cut (arrive ready duration deadline : Nat) :
    (∃ t : Nat, arrive ≤ t ∧ ready ≤ t ∧ t + duration ≤ deadline) ↔
      max arrive ready + duration ≤ deadline := by
  constructor
  · rintro ⟨t, a, b, c⟩
    have h := max_le a b
    omega
  · intro h
    exact ⟨max arrive ready, le_max_left _ _, le_max_right _ _, h⟩

theorem ack_only_cannot_reflect
    {V : Type} {oldView newView : V} (h : oldView = newView) :
    ¬ ∃ (act : V → Bool), act oldView = true ∧ act newView = false := by
  rintro ⟨act, a, b⟩
  rw [h,b] at a
  contradiction

theorem unrelated_gate {K : Type} [DecidableEq K] (f : K → Nat)
    (changed unaffected : K) (h : unaffected ≠ changed)
    (g p a : Nat) :
    authorized (if unaffected = changed then g else f unaffected) p a ↔
      authorized (f unaffected) p a := by simp [h]

end InstallCut
