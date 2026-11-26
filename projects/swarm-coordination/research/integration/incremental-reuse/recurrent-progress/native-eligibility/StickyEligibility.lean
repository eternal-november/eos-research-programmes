import Mathlib

namespace StickyEligibility

def InfOften (p : ℕ → Prop) : Prop := ∀ n, ∃ m, n ≤ m ∧ p m

def Weak (enabled taken : ℕ → Prop) : Prop :=
  InfOften (fun n => ¬ enabled n ∨ taken n)

def Strong (enabled taken : ℕ → Prop) : Prop :=
  InfOften enabled → InfOften taken

theorem strong_implies_weak (E T : ℕ → Prop) (h : Strong E T) : Weak E T := by
  intro n
  by_contra! hnever
  have ha : ∀ m, n ≤ m → E m ∧ ¬ T m := by
    intro m hm
    simpa using hnever m hm
  have hinf : InfOften E := by
    intro k
    exact ⟨max n k, le_max_right _ _, (ha _ (le_max_left _ _)).1⟩
  obtain ⟨m,hm,ht⟩ := h hinf n
  exact (ha _ hm).2 ht

theorem sticky_weak_implies_strong (E T : ℕ → Prop)
    (sticky : ∀ n, E n → ¬ T n → E (n+1)) (hweak : Weak E T) : Strong E T := by
  intro hinf n
  by_contra! hnone
  obtain ⟨i,hi,he⟩ := hinf n
  have htrail : ∀ k, E (i+k) := by
    intro k
    induction k with
    | zero => simpa using he
    | succ k ih =>
      exact sticky (i+k) ih (hnone (i+k) (by omega))
  obtain ⟨m,hm,hno|ht⟩ := hweak i
  · have heq : i+(m-i)=m := by omega
    exact hno (heq ▸ htrail (m-i))
  · exact hnone _ (by omega) ht

theorem reserve_rows (cap need tx rx addTx addRx : ℕ) :
    tx+addTx ≤ cap-need ∧ rx+addRx ≤ cap-need ∧ need ≤ cap ↔
    tx+addTx+need ≤ cap ∧ rx+addRx+need ≤ cap := by
  omega

#print axioms strong_implies_weak
#print axioms sticky_weak_implies_strong
#print axioms reserve_rows

end StickyEligibility
