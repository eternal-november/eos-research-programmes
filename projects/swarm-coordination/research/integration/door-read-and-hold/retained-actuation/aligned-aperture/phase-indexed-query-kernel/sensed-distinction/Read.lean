import Lean.Elab.Tactic.Omega

namespace ApertureRead
theorem overlapping_offsets {I : Type} (d : I → Int) (i j : I) (e : Int)
    (a : ∀ k, d i ≤ d k) (b : ∀ k, d k ≤ d j) :
    (∃ offset : Int, ∀ k, -e ≤ d k + offset ∧ d k + offset ≤ e) ↔
      d j - d i ≤ 2 * e := by
  constructor
  · rintro ⟨offset,h⟩
    have x := (h i).1
    have y := (h j).2
    omega
  · intro h
    refine ⟨-e - d i, ?_⟩
    intro k
    have x := a k
    have y := b k
    omega
end ApertureRead
