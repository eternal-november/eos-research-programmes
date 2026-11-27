import Mathlib
namespace Rewind

structure Row where
  endpoint : Nat
  bytes : Nat
  required : Bool

def one : List Row := [⟨0,60,false⟩,⟨1,173,true⟩,⟨2,60,false⟩,⟨1,173,true⟩]
def two : List Row := [⟨2,60,false⟩,⟨1,173,true⟩,⟨0,60,false⟩,⟨1,173,true⟩]
def charge (rows : List Row) (e extra : Nat) : Nat :=
  (rows.map fun r => r.bytes * (if r.endpoint = e then 1+extra else 1)).sum
def edge (rows : List Row) (e : Nat) : Nat :=
  ((rows.filter fun r => r.endpoint == e).map Row.bytes).sum

theorem same_last : charge one 0 0 = charge two 0 0 ∧
    (∀ e, edge one e = edge two e) := by
  constructor
  · decide
  · intro e
    by_cases h0 : e = 0
    · subst e; decide
    by_cases h1 : e = 1
    · subst e; decide
    by_cases h2 : e = 2
    · subst e; decide
    simp [edge, one, two, Ne.symm h0, Ne.symm h1, Ne.symm h2]

theorem different_after_rewind :
    ¬ charge (one.take 2) 0 4 ≤ 466 ∧ charge (two.take 2) 0 4 ≤ 466 := by decide

#print axioms same_last
#print axioms different_after_rewind
end Rewind
