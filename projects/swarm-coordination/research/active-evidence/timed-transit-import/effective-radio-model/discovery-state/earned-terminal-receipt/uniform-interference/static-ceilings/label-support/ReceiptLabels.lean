import Mathlib
namespace ReceiptLabels

def Conflict {K : Type} (admitted : List K → Prop) (x y : K) : Prop :=
  x ≠ y ∧ ∃ window, admitted window ∧ x ∈ window ∧ y ∈ window

def ExactOnWindows {K Tag : Type} (admitted : List K → Prop) (tag : K → Tag) : Prop :=
  ∀ window, admitted window →
    ∀ ⦃x y⦄, x ∈ window → y ∈ window → tag x = tag y → x = y

theorem exact_iff_separates_conflict {K Tag : Type}
    (admitted : List K → Prop) (tag : K → Tag) :
    ExactOnWindows admitted tag ↔ ∀ x y, Conflict admitted x y → tag x ≠ tag y := by
  constructor
  · intro hex x y hconf htag
    obtain ⟨hxy, window, hw, hx, hy⟩ := hconf
    exact hxy (hex window hw hx hy htag)
  · intro h window hw x y hx hy htag
    by_contra hxy
    exact h x y ⟨hxy, window, hw, hx, hy⟩ htag

def PairWindow {K : Type} (window : List K) : Prop :=
  ∃ x y : K, window = [x,y]

theorem two_slots_can_force_all_labels {n m : Nat}
    (tag : Fin n → Fin m) (ok : ExactOnWindows PairWindow tag) : n ≤ m := by
  have h : Function.Injective tag := by
    intro x y e
    exact ok [x,y] ⟨x,y,rfl⟩ (by simp) (by simp) e
  simpa using Fintype.card_le_of_injective tag h

theorem rebind_needs_a_distinction {Obs : Type}
    (allow : Obs → Bool) (old stale_current : Obs)
    (same : old = stale_current) (retired : allow old = false)
    (owed : allow stale_current = true) : False := by
  rw [same, owed] at retired
  cases retired

#print axioms rebind_needs_a_distinction
#print axioms exact_iff_separates_conflict
#print axioms two_slots_can_force_all_labels
end ReceiptLabels
