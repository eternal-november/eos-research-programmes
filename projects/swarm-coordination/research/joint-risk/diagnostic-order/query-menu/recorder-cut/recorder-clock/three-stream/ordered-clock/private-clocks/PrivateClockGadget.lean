import Mathlib

namespace PrivateClockGadget

def center (polarity : Bool) : ℝ := if polarity then 1 else 0

def admissible (d residual : ℝ) : Prop := |residual - d| ≤ 9 / 4

def movedFailure (d : ℝ) (polarity : Bool) : Prop :=
  admissible d (center polarity + 2) ∧ admissible d (center polarity - 2)

theorem regularPair (d : ℝ) (polarity : Bool) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    admissible d (center polarity) := by
  unfold admissible
  rw [abs_le]
  have hc0 : 0 ≤ center polarity := by cases polarity <;> simp [center]
  have hc1 : center polarity ≤ 1 := by cases polarity <;> simp [center]
  exact ⟨by linarith, by linarith⟩

theorem movedFailure_iff (d : ℝ) (polarity : Bool) :
    movedFailure d polarity ↔ center polarity - 1 / 4 ≤ d ∧ d ≤ center polarity + 1 / 4 := by
  unfold movedFailure admissible
  rw [abs_le, abs_le]
  constructor
  · rintro ⟨⟨ha, hb⟩, ⟨hc, hd⟩⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨ha, hb⟩
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

theorem gapIsolated (gap a b d : ℝ) (hgap : gap ≤ -10 ∨ 10 ≤ gap)
    (ha0 : 0 ≤ a) (ha2 : a ≤ 2) (hb0 : 0 ≤ b) (hb3 : b ≤ 3)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    ¬ admissible d (gap + b - a) := by
  intro h
  have hh := abs_le.mp h
  rcases hgap with hneg | hpos <;> linarith

theorem signOfOffset (d : ℝ) (p : Bool) (h : movedFailure d p) :
    decide ((1 : ℝ) / 2 ≤ d) = p := by
  have h' := (movedFailure_iff d p).mp h
  cases p with
  | false =>
    have htop : d ≤ 1 / 4 := by simpa [center] using h'.2
    have hnot : ¬ (1 : ℝ) / 2 ≤ d := by linarith
    exact decide_eq_false hnot
  | true =>
    have hbot : (1 : ℝ) - 1 / 4 ≤ d := by simpa [center] using h'.1
    have hyes : (1 : ℝ) / 2 ≤ d := by linarith
    exact decide_eq_true hyes

theorem literalEquivalence {α : Type*} (clauses : List (List (α × Bool))) :
    (∃ d : α → ℝ, (∀ x, 0 ≤ d x ∧ d x ≤ 1) ∧
        ∀ c ∈ clauses, ∃ p ∈ c, movedFailure (d p.1) p.2) ↔
      ∃ t : α → Bool, ∀ c ∈ clauses, ∃ p ∈ c, t p.1 = p.2 := by
  constructor
  · rintro ⟨d, _, hd⟩
    refine ⟨fun x => decide ((1 : ℝ) / 2 ≤ d x), ?_⟩
    intro c hc
    obtain ⟨p, hp, hm⟩ := hd c hc
    exact ⟨p, hp, signOfOffset _ _ hm⟩
  · rintro ⟨t, ht⟩
    refine ⟨fun x => center (t x), ?_, ?_⟩
    · intro x
      change 0 ≤ center (t x) ∧ center (t x) ≤ 1
      cases ht : t x <;> simp [center]
    · intro c hc
      obtain ⟨p, hp, hh⟩ := ht c hc
      refine ⟨p, hp, (movedFailure_iff _ _).2 ?_⟩
      change center p.2 - 1 / 4 ≤ center (t p.1) ∧ center (t p.1) ≤ center p.2 + 1 / 4
      rw [hh]
      constructor <;> linarith

#print axioms regularPair
#print axioms movedFailure_iff
#print axioms gapIsolated
#print axioms signOfOffset
#print axioms literalEquivalence

end PrivateClockGadget
