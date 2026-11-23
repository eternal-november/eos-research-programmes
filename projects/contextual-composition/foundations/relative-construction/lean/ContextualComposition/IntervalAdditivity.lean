module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-! Nonnegative additivity on the unit interval forces real linearity, without any continuity assumption. -/

public section
namespace ContextualComposition.IntervalAdditivity

theorem linear (f : ℝ → ℝ) (positive : ∀ x, 0 ≤ x → x ≤ 1 → 0 ≤ f x)
    (add : ∀ x y, 0 ≤ x → 0 ≤ y → x+y ≤ 1 → f (x+y) = f x + f y)
    (x : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1) : f x = x * f 1 := by
  have hz : f 0 = 0 := by have h := add 0 0 le_rfl le_rfl (by norm_num); simp only [zero_add] at h; linarith
  have mono (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) : f a ≤ f b := by
    have e := add a (b-a) ha (by linarith) (by linarith)
    rw [add_sub_cancel] at e
    linarith [positive (b-a) (by linarith) (by linarith)]
  have scaled (a : ℝ) (ha : 0 ≤ a) (n : ℕ) : (n:ℝ)*a ≤ 1 → f ((n:ℝ)*a) = n*f a := by
    induction n with
    | zero => simp [hz]
    | succ n ih =>
      intro hn
      rw [Nat.cast_succ,add_mul,one_mul] at hn ⊢
      rw [add _ _ (mul_nonneg (Nat.cast_nonneg _) ha) ha hn,ih (by linarith)]
      ring
  have rat (r : ℚ) (hr : 0 ≤ (r:ℝ)) (hr' : (r:ℝ) ≤ 1) : f r = (r:ℝ)*f 1 := by
    have den : 0 < (r.den : ℝ) := Nat.cast_pos.mpr r.den_pos
    have hn : 0 ≤ r.num := Rat.num_nonneg.mpr (by exact_mod_cast hr)
    have hcast : (r.num.toNat : ℝ) = (r.num : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hn
    have repr : (r:ℝ) = (r.num.toNat:ℝ)*(1/(r.den:ℝ)) := by rw [hcast,Rat.cast_def]; ring
    have one : (r.den:ℝ)*(1/(r.den:ℝ)) = 1 := by field_simp
    have hp := scaled (1/(r.den:ℝ)) (by positivity) r.den one.le
    rw [one] at hp
    rw [repr,scaled _ (by positivity) _ (repr ▸ hr'),hp]
    field_simp
  have hnon := positive 1 zero_le_one le_rfl
  have hfx := positive x hx hx'
  have hub := mono x 1 hx hx' le_rfl
  rcases hnon.eq_or_lt with he | hp
  · rw [← he]; linarith
  apply le_antisymm
  · by_contra! h
    have lt := (lt_div_iff₀ hp).mpr h
    obtain ⟨r,hr,hr'⟩ := exists_rat_btwn lt
    have rb : (r:ℝ) ≤ 1 := hr'.le.trans ((div_le_one hp).mpr hub)
    have hmono := mono x r hx hr.le rb
    rw [rat r (hx.trans hr.le) rb] at hmono
    exact (lt_div_iff₀ hp).mp hr' |>.not_ge hmono
  · by_contra! h
    have lt := (div_lt_iff₀ hp).mpr h
    obtain ⟨r,hr,hr'⟩ := exists_rat_btwn lt
    have rb : 0 ≤ (r:ℝ) := (div_nonneg hfx hp.le).trans hr.le
    have hmono := mono r x rb hr'.le hx'
    rw [rat r rb (hr'.le.trans hx')] at hmono
    exact (div_lt_iff₀ hp).mp hr |>.not_ge hmono

end ContextualComposition.IntervalAdditivity
