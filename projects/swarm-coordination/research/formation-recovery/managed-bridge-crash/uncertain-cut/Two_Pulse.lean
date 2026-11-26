import Mathlib

namespace TwoPulse

noncomputable def first (v d T : ℝ) := 4*d/T^2-3*v/T
noncomputable def second (v d T : ℝ) := -4*d/T^2+v/T

theorem terminal_rest (v d T : ℝ) (h : T ≠ 0) :
    v+(T/2)*(first v d T+second v d T)=0 := by
  unfold first second
  field_simp [h] <;> ring

theorem displacement (v d T : ℝ) (h : T ≠ 0) :
    v*T+(T/2)^2*(3*first v d T+second v d T)/2=d := by
  unfold first second
  field_simp [h] <;> ring

theorem residual_under_common_impulse (v w a : ℝ) :
    (v+a)-(w+a)=v-w := by ring

noncomputable def before (v d s T : ℝ) := 2*d/(s*T)-(T+s)*v/(s*T)
noncomputable def after (v d s T : ℝ) := -2*d/((T-s)*T)+s*v/((T-s)*T)

theorem switched_terminal_rest (v d s T : ℝ) (hs : s ≠ 0)
    (h : T ≠ 0) (h2 : T-s ≠ 0) :
    v+s*before v d s T+(T-s)*after v d s T=0 := by
  unfold before after
  field_simp [hs,h,h2] <;> ring

theorem switched_displacement (v d s T : ℝ) (hs : s ≠ 0)
    (h : T ≠ 0) (h2 : T-s ≠ 0) :
    v*T+(T*s-s^2/2)*before v d s T+(T-s)^2*after v d s T/2=d := by
  unfold before after
  field_simp [hs,h,h2] <;> ring

end TwoPulse

#print axioms TwoPulse.terminal_rest
#print axioms TwoPulse.displacement
#print axioms TwoPulse.residual_under_common_impulse
#print axioms TwoPulse.switched_terminal_rest
#print axioms TwoPulse.switched_displacement
