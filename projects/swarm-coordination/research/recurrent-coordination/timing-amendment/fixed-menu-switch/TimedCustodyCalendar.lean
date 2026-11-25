import Mathlib

namespace TimedCustodyCalendar

def Slot (gap : Nat → Nat) (prev expiry tm : Nat) : Prop :=
  expiry ≤ tm ∧ prev + gap tm ≤ tm

/-- The law can vary with time; for a fixed queried slot an earlier predecessor
    can never hurt availability. -/
theorem earlier_predecessor (g : Nat → Nat) (p q e t : Nat)
    (hp : p ≤ q) (h : Slot g q e t) : Slot g p e t := by
  exact ⟨h.1, le_trans (Nat.add_le_add_right hp _) h.2⟩

/-- A prefix threshold can replace the old expiry only if the real gap
    predicate is still tested. This is the induction step for the certificate. -/
theorem replace_expiry_by_least_slot
    (g : Nat → Nat) (early actual e m t : Nat)
    (hle : early ≤ actual) (hm : Slot g early e m)
    (least : ∀ u, Slot g early e u → m ≤ u) :
    Slot g actual e t ↔ m ≤ t ∧ actual + g t ≤ t := by
  constructor
  · intro ht
    exact ⟨least t (earlier_predecessor g early actual e t hle ht), ht.2⟩
  · rintro ⟨a,b⟩
    exact ⟨le_trans hm.1 a,b⟩

def Two (expiry : Nat) (s t : Nat) : Prop :=
  1 ≤ s ∧ s + 1 ≤ t ∧ expiry ≤ t ∧ t ≤ 2

theorem two_transfer_deadline_split :
    (∃ s t, Two 2 s t) ∧ ¬ (∃ s t, Two 3 s t) := by
  constructor
  · exact ⟨1,2,by unfold Two; omega⟩
  · rintro ⟨s,t,h⟩
    unfold Two at h
    omega

#print axioms earlier_predecessor
#print axioms replace_expiry_by_least_slot
#print axioms two_transfer_deadline_split

end TimedCustodyCalendar
