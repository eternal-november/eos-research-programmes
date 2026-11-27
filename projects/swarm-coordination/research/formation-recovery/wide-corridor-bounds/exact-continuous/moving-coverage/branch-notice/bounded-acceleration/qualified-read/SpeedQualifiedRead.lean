import Mathlib
namespace SpeedQualifiedRead

theorem cap_obstruction (sigma cut k a w r v : ℝ) (ha : 0<a)
  (hr : r ≤ cut)
  (kneed : k ≤ v+a*(sigma-r)) (hq : |v| ≤ w) :
  r ≤ min cut (sigma-(k-w)/a) := by
  have hv : v ≤ w := (abs_le.mp hq).2
  have h : k-w ≤ a*(sigma-r) := by linarith
  have hg : (k-w)/a ≤ sigma-r := (div_le_iff₀ ha).2 (by nlinarith)
  exact le_min hr (by linarith)

theorem cut_attains_cap_on_stroke (sigma cut k a w : ℝ) (ha : 0<a)
  (hw : 0≤w)
  (hv : 0 ≤ k-a*(sigma-cut)) :
  let r := min cut (sigma-(k-w)/a)
  let v := k-a*(sigma-r)
  0 ≤ v ∧ v ≤ w := by
  dsimp
  by_cases H : cut ≤ sigma-(k-w)/a
  · rw [min_eq_left H]
    have h : k-w ≤ (sigma-cut)*a := (div_le_iff₀ ha).1 (by linarith)
    constructor <;> nlinarith
  · rw [min_eq_right (le_of_not_ge H)]
    have h : a*((k-w)/a) = k-w := by field_simp
    constructor <;> nlinarith

#print axioms cap_obstruction
#print axioms cut_attains_cap_on_stroke
end SpeedQualifiedRead
