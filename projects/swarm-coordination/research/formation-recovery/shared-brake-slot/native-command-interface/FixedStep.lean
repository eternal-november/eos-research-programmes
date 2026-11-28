import Mathlib
namespace FixedStep
abbrev clip (lo hi u : ℤ) := max lo (min u hi)

def serial (p q u : ℤ) : ℤ :=
  clip 0 8 (clip (p-2) (p+2) (clip (p+(p-q)-1) (p+(p-q)+1) u))

def low (p q : ℤ) : ℤ := clip 0 8 (p + max (-2) (p-q-1))
def high (p q : ℤ) : ℤ := clip 0 8 (p + min 2 (p-q+1))

private theorem overlap (a b c d u : ℤ)
    (h : max a c ≤ min b d) :
    clip c d (clip a b u) = clip (max a c) (min b d) u := by
  simp only [clip, max_def, min_def] at *
  split_ifs at * <;> omega

private theorem image (a b u : ℤ) (h : a ≤ b) :
    clip 0 8 (clip a b u) = clip (clip 0 8 a) (clip 0 8 b) u := by
  simp only [clip, max_def, min_def]
  split_ifs <;> omega

theorem normalize (p q u : ℤ) (h : -2 ≤ p-q ∧ p-q ≤ 2) :
    serial p q u = clip (low p q) (high p q) u := by
  have lo : max (p+(p-q)-1) (p-2) = p+max (-2) (p-q-1) := by
    simp only [max_def]
    split_ifs <;> omega
  have hi : min (p+(p-q)+1) (p+2) = p+min 2 (p-q+1) := by
    simp only [min_def]
    split_ifs <;> omega
  have inter : max (p+(p-q)-1) (p-2) ≤ min (p+(p-q)+1) (p+2) := by
    simp only [max_def, min_def]
    split_ifs <;> omega
  unfold serial low high
  rw [overlap _ _ _ _ _ inter, image _ _ _ inter, lo, hi]

private theorem bounds (x : ℤ) : 0 ≤ clip 0 8 x ∧ clip 0 8 x ≤ 8 := by
  simp only [clip, max_def, min_def]
  split_ifs <;> omega

theorem endpoint_zero (p q : ℤ) (h : -2 ≤ p-q ∧ p-q ≤ 2) :
    serial p q 0 = low p q := by
  rw [normalize p q 0 h]
  have a : 0 ≤ low p q := bounds _ |>.1
  have b : 0 ≤ high p q := bounds _ |>.1
  change max (low p q) (min 0 (high p q)) = low p q
  rw [min_eq_left b, max_eq_left a]

theorem endpoint_eight (p q : ℤ) (h : -2 ≤ p-q ∧ p-q ≤ 2) :
    serial p q 8 = high p q := by
  rw [normalize p q 8 h]
  have hl : low p q ≤ high p q := by
    unfold low high
    simp only [clip, max_def, min_def]
    split_ifs <;> omega
  change max (low p q) (min 8 (high p q)) = high p q
  have hh : high p q ≤ 8 := bounds _ |>.2
  rw [min_eq_right hh, max_eq_right hl]

theorem interface_iff (p q r : ℤ)
    (hq : -2 ≤ p-q ∧ p-q ≤ 2) (hr : -2 ≤ p-r ∧ p-r ≤ 2) :
    (∀ u : ℤ, serial p q u = serial p r u) ↔
      low p q = low p r ∧ high p q = high p r := by
  constructor
  · intro h
    have a := h 0
    have b := h 8
    rw [endpoint_zero p q hq, endpoint_zero p r hr] at a
    rw [endpoint_eight p q hq, endpoint_eight p r hr] at b
    exact ⟨a, b⟩
  · rintro ⟨a, b⟩ u
    rw [normalize p q u hq, normalize p r u hr, a, b]

example : serial 5 3 0 = 6 ∧ serial 5 5 0 = 4 ∧ serial 5 7 0 = 3 := by decide

theorem equal_at_one : ∀ u : ℤ, serial 0 1 u = serial 0 2 u := by
  apply (interface_iff 0 1 2 (by decide) (by decide)).mpr
  decide

-- For fixed positive integral dt, the command differences see jerk times
-- dt squared and acceleration times dt. This is the exact arithmetic lift.
def serialDt (p q u dt : ℤ) : ℤ :=
  clip 0 8
    (clip (p-2*dt) (p+2*dt)
      (clip (p+(p-q)-dt^2) (p+(p-q)+dt^2) u))

example : serialDt 0 1 8 2 = 3 ∧ serialDt 0 2 8 2 = 2 := by decide

end FixedStep
#print axioms FixedStep.normalize
#print axioms FixedStep.interface_iff
