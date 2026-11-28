import Mathlib

namespace TemporalScope

variable {A : Type} [DecidableEq A]

def retain (w : Finset A) : List (Finset A) → Finset A
  | [] => w
  | u :: rest => retain (w \ u) rest

theorem one_step (w u : Finset A) : w.card - u.card ≤ (w \ u).card := by
  rw [Finset.card_sdiff]
  exact Nat.sub_le_sub_left (Finset.card_le_card Finset.inter_subset_left) _

theorem every_coordinated_schedule (w : Finset A) (us : List (Finset A)) :
    w.card - (us.map Finset.card).sum ≤ (retain w us).card := by
  induction us generalizing w with
  | nil => simp [retain]
  | cons u us ih =>
    have h := one_step w u
    have ih := ih (w \ u)
    simp only [List.map_cons, List.sum_cons, retain]
    omega

def takeCounts (n : Nat) : List Nat → List Nat
  | [] => []
  | b :: rest => min n b :: takeCounts (n - b) rest

theorem allocated_count (n : Nat) (bs : List Nat) :
    (takeCounts n bs).sum = min n bs.sum := by
  induction bs generalizing n with
  | nil => simp [takeCounts]
  | cons b bs ih =>
    simp only [takeCounts, List.sum_cons, ih]
    omega

theorem allocated_under_caps (n : Nat) (bs : List Nat) :
    List.Forall₂ (· ≤ ·) (takeCounts n bs) bs := by
  induction bs generalizing n with
  | nil => exact .nil
  | cons b bs ih =>
    exact .cons (Nat.min_le_right n b) (ih (n-b))

theorem optimal_count (n : Nat) (bs : List Nat) :
    n - (takeCounts n bs).sum = n - bs.sum := by
  rw [allocated_count]
  omega

end TemporalScope
