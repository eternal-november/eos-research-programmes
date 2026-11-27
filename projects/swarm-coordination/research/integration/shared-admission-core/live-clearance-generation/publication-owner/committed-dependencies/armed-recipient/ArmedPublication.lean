import Mathlib
namespace ArmedPublication

structure S where
  armA : Bool := false
  openA : Bool := false
  closeA : Bool := false
  paidA : Bool := false
  chooseB : Bool := false
  armB : Bool := false
  copyB : Option Bool := none
  openB : Bool := false
  paidB : Bool := false

-- This is the finite control projection, not the database/worker implementation.
inductive Step : S → S → Prop where
| issueA (s : S) (h : s.chooseB = false) :
    Step s {s with armA := true}
| installA (s : S) (h : s.armA = true) (k : s.closeA = false) :
    Step s {s with openA := true}
| closeA (s : S) :
    Step s {s with closeA := true}
| payA (s : S) (h : s.openA = true) (k : s.closeA = false) :
    Step s {s with paidA := true}
| chooseB (s : S) (h : s.armA = false ∨ s.closeA = true) :
    Step s {s with chooseB := true}
| issueB (s : S) (h : s.chooseB = true) :
    Step s {s with armB := true}
| copyB (s : S) (h : s.chooseB = true) :
    Step s {s with copyB := some s.paidA}
| installB (s : S) (h : s.armB = true) (k : s.copyB ≠ none) :
    Step s {s with openB := true}
| payB (s : S) (h : s.openB = true) (k : s.copyB = some false) :
    Step s {s with paidB := true}

def Invariant (s : S) : Prop :=
  (s.chooseB = true → s.armA = false ∨ s.closeA = true) ∧
  (s.openA = true → s.armA = true) ∧
  (s.copyB ≠ none → s.chooseB = true ∧ s.copyB = some s.paidA) ∧
  (s.paidB = true → s.copyB = some false)

theorem init : Invariant {} := by simp [Invariant]

theorem preserve {s t : S} (hs : Invariant s) (h : Step s t) : Invariant t := by
  cases h <;> simp only [Invariant] at * <;> grind

theorem no_double {s : S} (h : Invariant s) : ¬ (s.paidA = true ∧ s.paidB = true) := by
  unfold Invariant at h
  grind

#print axioms init
#print axioms preserve
#print axioms no_double
end ArmedPublication
