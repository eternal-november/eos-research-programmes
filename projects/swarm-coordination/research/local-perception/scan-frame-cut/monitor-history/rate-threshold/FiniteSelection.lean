import Mathlib

namespace MonitorRate

theorem finite_closed_selection {X : Type} [Fintype X] [Nonempty X]
    (lo hi : X → ℝ) (d : X → X → ℝ)
    (diag : ∀ i, d i i = 0)
    (triangle : ∀ i j k, d i k ≤ d i j + d j k) :
    (∃ f : X → ℝ, (∀ i, lo i ≤ f i ∧ f i ≤ hi i) ∧
      (∀ i j, f i - f j ≤ d i j)) ↔
    (∀ i j, lo i - hi j ≤ d i j) := by
  constructor
  · rintro ⟨f, h, hf⟩ i j
    linarith [(h i).1, (h j).2, hf i j]
  · intro h
    let f (i : X) := Finset.univ.sup' Finset.univ_nonempty (fun k => lo k - d k i)
    refine ⟨f, ?_, ?_⟩
    · intro i
      constructor
      · have hh := Finset.le_sup' (s := Finset.univ) (fun k => lo k - d k i)
              (Finset.mem_univ i)
        rw [diag, sub_zero] at hh
        exact hh
      · unfold f
        apply Finset.sup'_le
        intro k _
        linarith [h k i]
    · intro i j
      have hh : f i ≤ f j + d i j := by
        change Finset.univ.sup' Finset.univ_nonempty (fun k => lo k - d k i) ≤ f j + d i j
        apply Finset.sup'_le
        intro k _
        have hk : lo k - d k j ≤ f j := Finset.le_sup' (s := Finset.univ)
              (fun k => lo k - d k j) (Finset.mem_univ k)
        linarith [triangle k i j]
      linarith

end MonitorRate

#print axioms MonitorRate.finite_closed_selection
