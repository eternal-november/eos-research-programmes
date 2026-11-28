import Lean.Elab.Tactic.Omega
namespace RangeHandoff
theorem disjoint_upper (b p r w : Int) (h : b < p-r) :
  ¬ (w ≤ b ∧ p-r ≤ w) := by omega
theorem bridge_interior_fails_both (b p r w : Int) (hB : b < w) (hP : w < p-r) :
  ¬w ≤ b ∧ ¬p-r ≤ w := by omega
theorem all_prior_centers (pmin pmax r a b w : Int) (h : pmin ≤ pmax) :
  (a ≤ w ∧ w ≤ b ∧ (∀ p, pmin ≤ p → p ≤ pmax → p-r ≤ w ∧ w ≤ p+r)) ↔
  (max a (pmax-r) ≤ w ∧ w ≤ min b (pmin+r)) := by
  constructor
  · rintro ⟨ha,hb,hp⟩
    have v := hp pmin (by omega) h
    have u := hp pmax h (by omega)
    omega
  · rintro ⟨lo,hi⟩
    refine ⟨by omega,by omega,?_⟩
    intro p hp hq
    omega
end RangeHandoff
