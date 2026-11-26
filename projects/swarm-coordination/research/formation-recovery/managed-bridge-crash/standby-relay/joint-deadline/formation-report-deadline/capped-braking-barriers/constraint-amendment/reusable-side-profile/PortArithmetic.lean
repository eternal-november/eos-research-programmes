import Mathlib
namespace PortProfile

theorem shifted_predecessor (h y V v d : ℝ) (hh : h ≠ 0) :
    (V+y-v)^2/(2*h)-d =
      y^2/(2*h)+(V-v)/h*y-(d-(V-v)^2/(2*h)) := by
  field_simp
  ring

theorem strict_singleton_winner (s t δ b c : ℝ)
    (hδ : 0 < δ) (hsep : δ^2 ≤ (s-t)^2)
    (hb : b ≤ 1) (hc : 0 ≤ c) :
    t*s-t^2/2-δ^2*c/4 < s*s-s^2/2-δ^2*b/4 := by
  have h1 := mul_nonneg (sq_nonneg δ) hc
  have h2 := mul_nonneg (sq_nonneg δ) (sub_nonneg.mpr hb)
  nlinarith [sq_pos_of_pos hδ]

#print axioms shifted_predecessor
#print axioms strict_singleton_winner
end PortProfile
