import Mathlib

def good (s rho n a b : ℚ) : ℚ :=
  (1-s)*n + rho*a + (1-s-rho)*b

theorem shared_cap_bound (s r l n a b x : ℚ)
    (hr : 0 ≤ r) (hs : 0 ≤ 1-s-r)
    (hn : n ≤ 1-l) (ha : a ≤ l) (hb : 0 ≤ b)
    (risk : n+b ≤ x) :
    good s r n a b ≤ min ((1-s)*x + r*l) ((1-s)*x+r*(1-x)) := by
  have v : 0 ≤ 1-s := by linarith
  apply le_min
  · calc
      good s r n a b = (1-s)*(n+b)+r*(a-b) := by unfold good; ring
      _ ≤ (1-s)*x+r*l :=
        add_le_add (mul_le_mul_of_nonneg_left risk v)
          (mul_le_mul_of_nonneg_left (by linarith) hr)
  · calc
      good s r n a b = (1-s-r)*(n+b)+r*(n+a) := by unfold good; ring
      _ ≤ (1-s-r)*x+r*1 :=
        add_le_add (mul_le_mul_of_nonneg_left risk hs)
          (mul_le_mul_of_nonneg_left (by linarith) hr)
      _ = (1-s)*x+r*(1-x) := by ring

theorem conditional_linear_bound (s r l n a b x y : ℚ)
    (hr : 0 ≤ r) (hs : 0 ≤ 1-s-r)
    (hn : n ≤ x*(1-l)) (ha : a ≤ l) (hb : b ≤ y*l) :
    good s r n a b ≤ ((1-s)*x)*(1-l)+(r+(1-s-r)*y)*l := by
  have v : 0 ≤ 1-s := by linarith
  unfold good
  calc
    (1-s)*n + r*a + (1-s-r)*b
        ≤ (1-s)*(x*(1-l)) + r*l + (1-s-r)*(y*l) :=
          add_le_add (add_le_add (mul_le_mul_of_nonneg_left hn v)
            (mul_le_mul_of_nonneg_left ha hr)) (mul_le_mul_of_nonneg_left hb hs)
    _ = _ := by ring

theorem choose_high_or_low (base r k l x value : ℚ)
    (hk : 0 ≤ k) (hl : 0 ≤ l) (_hx : x ≤ 1)
    (upper1 : value ≤ base+r*l)
    (upper2 : value ≤ base+r*(1-x)) :
    value-k*l ≤ base + max 0 (r-k)*(1-x) := by
  by_cases c : k ≤ r
  · rw [max_eq_right (sub_nonneg.mpr c)]
    by_cases b : l ≤ 1-x
    · have v := mul_le_mul_of_nonneg_left b (sub_nonneg.mpr c)
      linarith
    · have v := mul_le_mul_of_nonneg_left (le_of_not_ge b) hk
      linarith
  · rw [max_eq_left (sub_nonpos.mpr (le_of_not_ge c)),zero_mul,add_zero]
    have v := mul_le_mul_of_nonneg_right (le_of_not_ge c) hl
    linarith

#print axioms shared_cap_bound
#print axioms conditional_linear_bound
#print axioms choose_high_or_low
