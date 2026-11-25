import Mathlib
namespace GuardedOption

theorem cutoff (s v p a l : ℚ) (hs : 0 < s) :
    a ≤ s*(v-p)+(1-s)*l ↔ p ≤ v-(a-(1-s)*l)/s := by
  have E : (a-(1-s)*l)/s ≤ v-p ↔ a-(1-s)*l ≤ (v-p)*s :=
    div_le_iff₀ hs
  constructor
  · intro h
    have h' : (a-(1-s)*l)/s ≤ v-p := E.mpr (by nlinarith only [h])
    linarith only [h']
  · intro h
    have h' : (a-(1-s)*l)/s ≤ v-p := by linarith only [h]
    have g := E.mp h'
    nlinarith only [g]

theorem noGrossTradeOnFailedSafety (guard joint surplus : Bool)
    (rule : joint = (guard && surplus)) (failed : guard = false) : joint = false := by
  simp [rule,failed]

theorem identicalNetPreference (s t p x p' x' cap : ℚ)
    (hs : 0 < s) (ht : 0 < t) :
    s*(cap*x-p) ≤ s*(cap*x'-p') ↔
    t*(cap*x-p) ≤ t*(cap*x'-p') := by
  rw [mul_le_mul_iff_right₀ hs, mul_le_mul_iff_right₀ ht]

#print axioms cutoff
#print axioms noGrossTradeOnFailedSafety
#print axioms identicalNetPreference
end GuardedOption
