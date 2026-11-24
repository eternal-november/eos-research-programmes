import Mathlib

namespace SwarmFormation
theorem extreme_endpoints_bridge_exact
    (left right : Set ℝ) (lmax rmin stop clearance range : ℝ)
    (hlmax : lmax ∈ left) (hrmin : rmin ∈ right)
    (hl : ∀ l ∈ left, l ≤ lmax)
    (hr : ∀ r ∈ right, rmin ≤ r)
    (hls : lmax ≤ stop - clearance)
    (hrs : stop + clearance ≤ rmin)
    (hc : 0 ≤ clearance) :
    (∃ l ∈ left, ∃ r ∈ right, clearance ≤ r-l ∧ r-l ≤ range) ↔
      clearance ≤ rmin-lmax ∧ rmin-lmax ≤ range := by
  constructor
  · rintro ⟨l, hl', r, hr', _, hb⟩
    have hll := hl l hl'
    have hrr := hr r hr'
    constructor <;> linarith
  · intro h
    exact ⟨lmax, hlmax, rmin, hrmin, h⟩

theorem extremes_dominate_every_other_gap
    (lmax rmin l r : ℝ) (hl : l ≤ lmax) (hr : rmin ≤ r) :
    rmin-lmax ≤ r-l := by linarith

#print axioms extreme_endpoints_bridge_exact
#print axioms extremes_dominate_every_other_gap

-- A pair of movable survivors in the [0,10] corridor, outer anchors fixed.
def Terminal (f x y : ℚ) : Prop :=
  |x - 2| ≤ 2 ∧ |y - 8| ≤ 2 ∧
  x ≤ f-1 ∧ f+1 ≤ y ∧
  1 ≤ x ∧ x ≤ 7/2 ∧
  1 ≤ y-x ∧ y-x ≤ 7/2 ∧
  1 ≤ 10-y ∧ 10-y ≤ 7/2

theorem stopped_at_four_has_plan : Terminal 4 3 (13/2) := by
  norm_num [Terminal]

theorem stopped_at_six_has_plan : Terminal 6 (7/2) 7 := by
  norm_num [Terminal]

theorem no_shared_left_choice
    (x yLow yHigh : ℚ) :
    ¬ (Terminal 4 x yLow ∧ Terminal 6 x yHigh) := by
  rintro ⟨h4,h6⟩
  have hleft := h4.2.2.1
  have hright := h6.2.2.2.1
  have hrange := h6.2.2.2.2.2.2.2.1
  linarith

#print axioms stopped_at_four_has_plan
#print axioms stopped_at_six_has_plan
#print axioms no_shared_left_choice

theorem earliest_low_world_contact {t x y : ℚ}
    (hx : x ≤ 3) (hy : 8-t ≤ y) (link : y-x ≤ 7/2) :
    3/2 ≤ t := by linarith

theorem active_deadline_lower_bound {delay notice deadline before after : ℚ}
    (hNotice : 3/2 + delay ≤ notice)
    (hBefore : before ≤ 3) (hEnd : 7/2 ≤ after)
    (speed : after-before ≤ deadline-notice) :
    2 + delay ≤ deadline := by linarith

#print axioms earliest_low_world_contact
#print axioms active_deadline_lower_bound
end SwarmFormation
