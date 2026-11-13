import Mathlib

/-!
A small kernel-checked fragment of the task-specific elaboration situation.
This file does NOT formalize Hankel rank factorization, Eckart--Young,
all displayed categories, an empirical noise guarantee, or model selection.
It checks the comparison inference once its typed premises are supplied,
and exact arithmetic for the concrete reciprocal recurrence example.
-/
namespace ElaborationSituation

theorem robust_norm_gap
    {V : Type*} [NormedAddCommGroup V]
    {M : Type*} (prediction : M → V) (Y H G : V)
    (β c ε : ℝ)
    (noise : ‖H - Y‖ ≤ ε)
    (fit : ‖Y - G‖ ≤ c)
    (lower : ∀ m, β ≤ ‖Y - prediction m‖) :
    ∀ m, β - c - 2 * ε ≤ ‖H - prediction m‖ - ‖H - G‖ := by
  intro m
  have htri₁ := norm_sub_le_norm_sub_add_norm_sub Y H (prediction m)
  have htri₂ := norm_sub_le_norm_sub_add_norm_sub H Y G
  have hrev : ‖Y - H‖ = ‖H - Y‖ := norm_sub_rev Y H
  have hlower := lower m
  linarith

theorem robust_squared_gap
    (a b β c ε : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hε : 0 ≤ ε)
    (lower : β - ε ≤ a) (upper : b ≤ c + ε)
    (margin : c + 2 * ε < β) :
    0 < (β - ε)^2 - (c + ε)^2 ∧
    (β - ε)^2 - (c + ε)^2 ≤ a^2 - b^2 := by
  have hlo : 0 ≤ β - ε := by linarith
  have hup : 0 ≤ c + ε := by positivity
  have hsqa : (β - ε)^2 ≤ a^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr lower) (add_nonneg ha hlo)]
  have hsqb : b^2 ≤ (c + ε)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr upper) (add_nonneg hup hb)]
  constructor
  · have hprod : 0 < ((β - ε) - (c + ε)) * ((β - ε) + (c + ε)) :=
      mul_pos (by linarith) (by linarith)
    nlinarith
  · linarith

theorem approximate_transport_composes
    {V : Type*} [NormedAddCommGroup V] (x y z : V) (ε δ : ℝ)
    (first : ‖x - y‖ ≤ ε) (second : ‖y - z‖ ≤ δ) :
    ‖x - z‖ ≤ ε + δ := by
  exact (norm_sub_le_norm_sub_add_norm_sub x y z).trans (add_le_add first second)

noncomputable def reciprocalSequence (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem reciprocalSequence_pos (n : ℕ) : 0 < reciprocalSequence n := by
  unfold reciprocalSequence
  positivity

theorem reciprocalSequence_start : reciprocalSequence 0 = 1 := by
  norm_num [reciprocalSequence]

theorem reciprocalSequence_step (n : ℕ) :
    reciprocalSequence (n + 1) =
      reciprocalSequence n / (1 + reciprocalSequence n) := by
  unfold reciprocalSequence
  push_cast
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp

theorem reciprocal_coordinate (x : ℝ) (hx : 0 < x) :
    1 / (x / (1 + x)) = 1 / x + 1 := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have h1x : 1 + x ≠ 0 := by positivity
  field_simp

theorem hilbert2_lower_identity (u v : ℝ) :
    u^2 + u*v + v^2/3 - (u^2+v^2)/16 =
      (15/16 : ℝ) * (u + (8/15 : ℝ)*v)^2 + v^2/240 := by
  ring

theorem hilbert2_lower_quadratic (u v : ℝ) :
    (u^2+v^2)/16 ≤ u^2 + u*v + v^2/3 := by
  have hid := hilbert2_lower_identity u v
  have hp : 0 ≤ (15/16 : ℝ) * (u + (8/15 : ℝ)*v)^2 + v^2/240 := by
    positivity
  linarith

theorem concrete_squared_gap :
    (1/32 - 1/256 : ℝ)^2 - (0 + 1/256)^2 = 3/4096 := by
  norm_num

#print axioms robust_norm_gap
#print axioms robust_squared_gap
#print axioms reciprocalSequence_step
#print axioms hilbert2_lower_quadratic
end ElaborationSituation
