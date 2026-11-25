import Mathlib

namespace TailCut

def clip (h : Nat) : Option Nat → Nat
  | none => h
  | some t => min h t

def clear (h : Nat) : Option Nat → Prop
  | none => False
  | some t => t ≤ h

theorem paused_at_end (h : Nat) :
    clip h (some h) = clip h none ∧ clear h (some h) ∧ ¬ clear h none := by
  simp [clip, clear]

theorem strict_cut (h : Nat) (x : Option Nat) (p : clip h x < h) :
    clear h x := by
  cases x with
  | none => simp [clip] at p
  | some a =>
    simp [clip, clear] at *
    omega

theorem start_earliest {g r prev other actual : Nat}
    (monotone : prev ≤ other) (hg : g ≤ actual) (hr : other + r ≤ actual) :
    max g (prev + r) ≤ actual := by
  exact max_le hg (le_trans (Nat.add_le_add_right monotone _) hr)

#print axioms paused_at_end
#print axioms strict_cut
#print axioms start_earliest

end TailCut
