import Mathlib

/-- At first divergent receipt, a common earlier accepted prefix has size a.
Refused probe bytes still occupy the shared transmitter. -/
theorem adaptive_common_cut (c q y : ℕ) :
    (∃ a x : ℕ, 0 < x ∧ c < q+a+x ∧ a+x+y ≤ c ∧ q+a+y ≤ c) ↔
    (0 < q ∧ y < q ∧ q+y ≤ c) := by
  constructor
  · rintro ⟨a,x,hx,hit,tx,rx⟩
    omega
  · rintro ⟨hq,hy,hc⟩
    refine ⟨0,c+1-q,?_,?_,?_,?_⟩ <;> omega

/-- Separate probe sender, whose configured ceiling the selected native
receiver admission tests. The old duty needs a larger or different sender. -/
theorem separated_sender_cut (c q y p : ℕ) :
    (∃ x : ℕ, 0 < x ∧ x ≤ p ∧ p < q+x ∧ q+y ≤ c ∧ x+y ≤ c) ↔
    (0 < q ∧ 0 < p ∧ q+y ≤ c ∧ max 1 (p+1-q)+y ≤ c) := by
  constructor
  · rintro ⟨x,hx,hp,hit,ra,rb⟩
    omega
  · rintro ⟨hq,hp,ha,hb⟩
    refine ⟨max 1 (p+1-q),?_,?_,?_,?_,?_⟩ <;> omega

#print axioms adaptive_common_cut
#print axioms separated_sender_cut
