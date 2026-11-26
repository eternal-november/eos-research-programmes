import Mathlib

namespace TimedPermissions

theorem covered_ticks (a e t h : ℤ) (hh : 0 < h) :
    (∀ i : ℤ, t ≤ i → i < t+h → a ≤ i ∧ i < e) ↔ a ≤ t ∧ t ≤ e-h := by
  constructor
  · intro call
    have low := (call t (by omega) (by omega)).1
    have high := (call (t+h-1) (by omega) (by omega)).2
    omega
  · rintro ⟨low,high⟩ i hi hj
    omega

theorem dual_then_new (a e b f c d D t h r : ℤ) (hh : 0 < h) (hr : 0 < r) :
    (c ≤ t ∧ d ≤ t ∧
    (∀ i : ℤ, t ≤ i → i < t+h → a ≤ i ∧ i < e) ∧
    (∀ i : ℤ, t ≤ i → i < t+(h+r) → b ≤ i ∧ i < f ∧ i < D)) ↔
    max (max c d) (max a b) ≤ t ∧ t ≤ min (e-h) (min (f-h-r) (D-h-r)) := by
  have hd : (∀ i : ℤ, t ≤ i → i < t+h+r → b ≤ i ∧ i < f ∧ i < D) ↔
      b ≤ t ∧ t ≤ f-h-r ∧ t ≤ D-h-r := by
    constructor
    · intro z
      have lo := (z t (by omega) (by omega)).1
      have hi := (z (t+h+r-1) (by omega) (by omega)).2
      omega
    · intro z i hi hj
      omega
  rw [covered_ticks _ _ _ _ hh]
  simp only [← add_assoc, hd, max_le_iff, le_min_iff]
  tauto

theorem interval_helly_at_extrema {X : Type} (L R : X → ℤ) (imax imin : X)
    (lmax : ∀ i, L i ≤ L imax) (rmin : ∀ i, R imin ≤ R i)
    (compatible : ∀ i j, L i ≤ R j) :
    ∀ i, L i ≤ L imax ∧ L imax ≤ R i :=
  fun i => ⟨lmax i, le_trans (compatible imax imin) (rmin i)⟩

#print axioms covered_ticks
#print axioms dual_then_new
#print axioms interval_helly_at_extrema
end TimedPermissions
