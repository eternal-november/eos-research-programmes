import Mathlib

namespace SwarmFormation

structure IntInterval where
  lo : ℤ
  hi : ℤ

def IntInterval.Has (d : IntInterval) (y : ℤ) : Prop :=
  d.lo ≤ y ∧ y ≤ d.hi

def IntInterval.clip (d : IntInterval) : Option IntInterval :=
  if d.lo ≤ d.hi then some d else none

def Holds (d : Option IntInterval) (y : ℤ) : Prop :=
  match d with
  | none => False
  | some i => i.Has y

theorem holds_clip (d : IntInterval) (y : ℤ) :
    Holds d.clip y ↔ d.Has y := by
  unfold IntInterval.clip
  split
  · rfl
  · rename_i h
    exact ⟨False.elim, fun hy => h (le_trans hy.1 hy.2)⟩

theorem extend_exact (old localDomain : IntInterval) (low high y : ℤ)
    (hold : old.lo ≤ old.hi) (hgap : low ≤ high) :
    localDomain.Has y ∧
      (∃ x, old.Has x ∧ low ≤ y - x ∧ y - x ≤ high) ↔
    (IntInterval.mk (max localDomain.lo (old.lo + low))
      (min localDomain.hi (old.hi + high))).Has y := by
  simp only [IntInterval.Has, max_le_iff, le_min_iff]
  constructor
  · rintro ⟨⟨hl, hh⟩, x, ⟨hx₁,hx₂⟩, h₁, h₂⟩
    exact ⟨⟨hl, by omega⟩, ⟨hh, by omega⟩⟩
  · rintro ⟨⟨h₁,h₂⟩, h₃,h₄⟩
    refine ⟨⟨h₁,h₃⟩, max old.lo (y-high), ⟨le_max_left _ _, ?_⟩, ?_, ?_⟩
    · exact max_le (by omega) (by omega)
    · have hm : max old.lo (y-high) ≤ y-low := max_le (by omega) (by omega)
      omega
    · have hm := le_max_right old.lo (y-high)
      omega

def extend (old : Option IntInterval) (d : IntInterval) (low high : ℤ) :
    Option IntInterval := do
  let i ← old
  (IntInterval.mk (max d.lo (i.lo + low)) (min d.hi (i.hi + high))).clip

def Valid (d : Option IntInterval) : Prop :=
  match d with
  | none => True
  | some i => i.lo ≤ i.hi

theorem valid_clip (d : IntInterval) : Valid d.clip := by
  unfold IntInterval.clip
  split <;> rename_i h
  · exact h
  · exact True.intro

theorem valid_extend (old : Option IntInterval) (d : IntInterval) (low high : ℤ) :
    Valid (extend old d low high) := by
  cases old with
  | none => exact True.intro
  | some i => exact valid_clip _

theorem holds_extend (old : Option IntInterval) (d : IntInterval) (l h y : ℤ)
    (hv : Valid old) (hg : l ≤ h) :
    Holds (extend old d l h) y ↔
      d.Has y ∧ ∃ x, Holds old x ∧ l ≤ y - x ∧ y - x ≤ h := by
  cases old with
  | none => simp [extend, Holds]
  | some i =>
    change Holds (IntInterval.mk (max d.lo (i.lo+l)) (min d.hi (i.hi+h))).clip y
      ↔ d.Has y ∧ ∃ x, i.Has x ∧ l ≤ y-x ∧ y-x ≤ h
    rw [holds_clip]
    exact (extend_exact i d l h y hv hg).symm

def lastReach (start : IntInterval) (low high : ℤ) :
    List IntInterval → ℤ → Prop
  | [], y => start.Has y
  | d :: tail, y =>
      d.Has y ∧ ∃ x, lastReach start low high tail x ∧
        low ≤ y-x ∧ y-x ≤ high

def lastScan (start : IntInterval) (low high : ℤ) :
    List IntInterval → Option IntInterval
  | [] => start.clip
  | d :: tail => extend (lastScan start low high tail) d low high

theorem lastScan_valid (start : IntInterval) (low high : ℤ) (ds : List IntInterval) :
    Valid (lastScan start low high ds) := by
  cases ds with
  | nil => exact valid_clip start
  | cons d tail => exact valid_extend _ _ _ _

theorem lastScan_exact (start : IntInterval) (low high : ℤ) (hg : low ≤ high) :
    ∀ (ds : List IntInterval) (y : ℤ),
      Holds (lastScan start low high ds) y ↔ lastReach start low high ds y := by
  intro ds
  induction ds with
  | nil => exact holds_clip start
  | cons d tail ih =>
    intro y
    simp only [lastScan, lastReach]
    rw [holds_extend _ _ _ _ _ (lastScan_valid start low high tail) hg]
    simp only [ih]

#print axioms extend_exact
#print axioms lastScan_exact

def interp (a b u : ℝ) : ℝ := (1-u)*a + u*b

theorem preserve_affine_gap (x₀ y₀ x₁ y₁ lower upper u : ℝ)
    (hu : 0 ≤ u) (hv : u ≤ 1)
    (h0 : lower ≤ y₀-x₀ ∧ y₀-x₀ ≤ upper)
    (h1 : lower ≤ y₁-x₁ ∧ y₁-x₁ ≤ upper) :
    lower ≤ interp y₀ y₁ u - interp x₀ x₁ u ∧
    interp y₀ y₁ u - interp x₀ x₁ u ≤ upper := by
  unfold interp
  have hc : 0 ≤ 1-u := sub_nonneg.mpr hv
  constructor
  · nlinarith [mul_nonneg hc (sub_nonneg.mpr h0.1),
      mul_nonneg hu (sub_nonneg.mpr h1.1)]
  · nlinarith [mul_nonneg hc (sub_nonneg.mpr h0.2),
      mul_nonneg hu (sub_nonneg.mpr h1.2)]

theorem interp_speed_normalized (x₀ x₁ u v bound : ℝ)
    (h : |x₁-x₀| ≤ bound) :
    |interp x₀ x₁ u - interp x₀ x₁ v| ≤ |u-v| * bound := by
  have heq : interp x₀ x₁ u - interp x₀ x₁ v = (u-v)*(x₁-x₀) := by
    unfold interp
    ring
  rw [heq, abs_mul]
  exact mul_le_mul_of_nonneg_left h (abs_nonneg _)

#print axioms preserve_affine_gap
#print axioms interp_speed_normalized
end SwarmFormation
