import Mathlib

namespace ReturnWindow

-- Decoded from the separate graph replay; true means the alternate
-- mouth is closed. 'spent' means the relay at 13 is effective by slot 1.
def allows (closed spent : Bool) (next : ℕ) : Prop :=
  if closed then spent = true ∧ next = 6
  else next = 42 ∨ (spent = true ∧ next = 6)

theorem blindNeedsReserve (next : ℕ) (openSpent closedSpent : Bool)
    (ho : allows false openSpent next) (hc : allows true closedSpent next) :
    openSpent = true ∧ closedSpent = true ∧ next = 6 := by
  simp only [allows, Bool.false_eq_true, ite_false, ite_true] at ho hc
  rcases hc with ⟨hs, hn⟩
  simp [hn] at ho
  exact ⟨ho, hs, hn⟩

theorem beforeMoveCueSuffices (closed : Bool) :
    allows closed closed (if closed then 6 else 42) := by
  cases closed <;> simp [allows]

theorem existenceWithoutCue (openSpent closedSpent : Bool) :
    (∃ next, allows false openSpent next ∧ allows true closedSpent next)
    ↔ openSpent = true ∧ closedSpent = true := by
  constructor
  · rintro ⟨n, ho, hc⟩
    exact ⟨(blindNeedsReserve n openSpent closedSpent ho hc).1,
            (blindNeedsReserve n openSpent closedSpent ho hc).2.1⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨6, by simp [allows]⟩

#print axioms blindNeedsReserve
#print axioms beforeMoveCueSuffices
#print axioms existenceWithoutCue
end ReturnWindow
