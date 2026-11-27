import Mathlib
namespace StaticCeiling
theorem sparse_band (lo hi a tx : Nat) (_h : lo ≤ hi) :
    (∃ q : Nat, hi+a ≤ q ∧ tx+a ≤ q ∧ q < lo+2*a) ↔
    hi < lo+a ∧ tx < lo+a := by
  constructor
  · rintro ⟨q, hq₁, hq₂, hq₃⟩
    omega
  · intro w
    refine ⟨max (hi+a) (tx+a), le_max_left .., le_max_right .., ?_⟩
    exact max_lt (by omega) (by omega)

theorem b_first_obstruction (lo hi a b : Nat) (h : lo ≤ hi) (hb : a ≤ b) :
    ¬ ∃ q : Nat, hi+b+a ≤ q ∧ q < lo+2*a := by omega

theorem byte_only_key_obstruction (x a cap : Nat) :
    ¬ (x+a+a ≤ cap ∧ ¬ x+a+a ≤ cap) := by omega

theorem fixture_narrowing :
  (9 ≤ 17 ∧ 17 < 18 ∧ 9+10 ≤ 19 : Prop) := by omega
theorem shared_sender_distinct_duty
    (a b c p : Nat) (hbc : a ≤ b+c) :
    ¬ (p < 2*a ∧ a+b+c ≤ p) := by omega

theorem predicted_a_first_vs_late_no_cap
    (a b r p q : Nat) (hba : a ≤ b) (hR : r < 2*a+b)
    (dual_first : q < a ∨ p < 2*a ∨ 2*a+b ≤ r)
    (p_last : a+b ≤ p) (q_last : a+b ≤ q) (hp : 0 < a) : False := by omega

#print axioms shared_sender_distinct_duty
#print axioms predicted_a_first_vs_late_no_cap
#print axioms sparse_band
#print axioms b_first_obstruction
#print axioms byte_only_key_obstruction
#print axioms fixture_narrowing
end StaticCeiling
