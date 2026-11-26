import Mathlib

universe u v w

/-- Maps a retained world and an extension world into the same boundary. -/
def FullVerdict {R : Type u} {E : Type v} {B : Type w}
    (rBoundary : R → B) (eBoundary : E → B)
    (retained : R → ℕ) (extra due : E → ℕ) : Prop :=
  ∀ (r : R) (e : E), rBoundary r = eBoundary e →
    retained r + extra e ≥ due e

theorem minimum_is_exact {R : Type u} {E : Type v} {B : Type w}
    (rBoundary : R → B) (eBoundary : E → B)
    (retained : R → ℕ) (extra due : E → ℕ) (lo : B → ℕ)
    (lower : ∀ r, lo (rBoundary r) ≤ retained r)
    (witness : ∀ e, ∃ r, rBoundary r = eBoundary e ∧ retained r = lo (eBoundary e)) :
    FullVerdict rBoundary eBoundary retained extra due ↔
      ∀ e, lo (eBoundary e) + extra e ≥ due e := by
  constructor
  · intro hf e
    obtain ⟨r, hr, hs⟩ := witness e
    simpa [hs] using hf r e hr
  · intro hp r e same
    have a := lower r
    rw [same] at a
    exact Nat.le_trans (hp e) (Nat.add_le_add_right a _)

theorem distinct_minima_separated (a b : ℕ) (h : a ≠ b) :
    ∃ d, ¬ ((d ≤ a) ↔ (d ≤ b)) := by
  rcases lt_or_gt_of_ne h with hab | hba
  · exact ⟨b, fun eq => (Nat.not_le_of_gt hab) (eq.mpr (Nat.le_refl _))⟩
  · exact ⟨a, fun eq => (Nat.not_le_of_gt hba) (eq.mp (Nat.le_refl _))⟩

theorem retained_proof_checks_after_filter {R : Type u} {E : Type v} {B : Type w}
    (rBoundary : R → B) (eBoundary : E → B)
    (retained : R → ℕ) (extra due : E → ℕ) (lo : B → ℕ)
    (lower : ∀ r, lo (rBoundary r) ≤ retained r)
    (permitted : R → E → Prop)
    (h : ∀ e, lo (eBoundary e) + extra e ≥ due e) :
    ∀ r e, permitted r e → rBoundary r = eBoundary e →
      due e ≤ retained r + extra e := by
  intro r e _ same
  have a := lower r
  rw [same] at a
  exact Nat.le_trans (h e) (Nat.add_le_add_right a _)

#print axioms minimum_is_exact
#print axioms distinct_minima_separated
#print axioms retained_proof_checks_after_filter
