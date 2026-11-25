import Mathlib
namespace AsymmetricRelayLens

/-- The axis exclusions of the two open, overlapping disks. -/
theorem common_axis {x c r : ℝ} (h : c < r) (hc : 0 ≤ c) :
    ((x ≤ c-r ∨ c+r ≤ x) ∧ (x ≤ -c-r ∨ -c+r ≤ x)) ↔
      (x ≤ -c-r ∨ c+r ≤ x) := by
  constructor
  · rintro ⟨h1 | h1, h2 | h2⟩
    · exact Or.inl h2
    · exfalso; linarith
    · exact Or.inr h1
    · exact Or.inr h1
  · rintro (hx | hx)
    · exact ⟨Or.inl (by linarith), Or.inl hx⟩
    · exact ⟨Or.inr hx, Or.inr (by linarith)⟩

theorem one_link_necessary {x a c r rp rm : ℝ} (h : c < r) (hc : 0 ≤ c)
    (hr : x-a ≥ -rp) (hl : x+a ≤ rm)
    (h1 : x ≤ c-r ∨ c+r ≤ x)
    (h2 : x ≤ -c-r ∨ -c+r ≤ x) :
    a+c+r ≤ max rp rm := by
  rcases (common_axis h hc).mp ⟨h1,h2⟩ with hx|hx
  · exact le_trans (by linarith) (le_max_left rp rm)
  · exact le_trans (by linarith) (le_max_right rp rm)

theorem right_arc_other_disk {x c y : ℝ} (hc : 0 ≤ c) (hx : 0 ≤ x) :
    (x-c)^2+y^2 ≤ (x+c)^2+y^2 := by
  nlinarith [mul_nonneg hc hx]

theorem hybrid_lower {a b t1 t2 : ℝ}
    (h : a ≤ t1 ∨ a ≤ t2 ∨ b ≤ t1 ∨ b ≤ t2) :
    min a b ≤ max t1 t2 := by
  rcases h with h|h|h|h
  · exact (min_le_left a b).trans (h.trans (le_max_left t1 t2))
  · exact (min_le_left a b).trans (h.trans (le_max_right t1 t2))
  · exact (min_le_right a b).trans (h.trans (le_max_left t1 t2))
  · exact (min_le_right a b).trans (h.trans (le_max_right t1 t2))

end AsymmetricRelayLens

#print axioms AsymmetricRelayLens.common_axis
#print axioms AsymmetricRelayLens.one_link_necessary
#print axioms AsymmetricRelayLens.right_arc_other_disk
#print axioms AsymmetricRelayLens.hybrid_lower
