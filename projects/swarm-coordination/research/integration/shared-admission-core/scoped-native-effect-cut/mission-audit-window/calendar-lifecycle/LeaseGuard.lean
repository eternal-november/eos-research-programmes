import Mathlib

namespace ScopedLease

variable {T : Type} [DecidableEq T]

structure State (T : Type) where
  remaining : Finset T
  blocked : Finset T
  settled : Prop

def hasCut (payload : Finset T) (unavailable : Finset T) : Prop :=
  ∃ t ∈ payload, t ∉ unavailable

def invariant (s : State T) : Prop :=
  s.settled ∨ hasCut s.remaining s.blocked

-- The receipt property is source-specific; equality of packet bytes
-- or an unacknowledged request is not a proof of this premise.
theorem edit_preserves (s : State T) (proposal : Finset T) (qualified : Prop)
    (sound : qualified → s.settled)
    (grant : qualified ∨ hasCut s.remaining proposal) :
    invariant ({s with blocked := proposal}) := by
  rcases grant with q | w
  · exact Or.inl (sound q)
  · exact Or.inr w

def advance (s : State T) (t : T) : State T :=
  { remaining := s.remaining.erase t
    blocked := s.blocked
    settled := s.settled ∨ (t ∈ s.remaining ∧ t ∉ s.blocked) }

-- The owned simulator dispatches upon a qualified cut. Erasure itself
-- cannot retroactively mark an unavailable cut as serviced.
theorem advance_preserves (s : State T) (t : T) (h : invariant s) :
    invariant (advance s t) := by
  rcases h with done | ⟨x, hx, hclear⟩
  · exact Or.inl (Or.inl done)
  · by_cases eq : x=t
    · subst x
      exact Or.inl (Or.inr ⟨hx,hclear⟩)
    · exact Or.inr ⟨x,Finset.mem_erase.mpr ⟨eq,hx⟩,hclear⟩

theorem complete (s : State T) (empty : s.remaining=∅) (h : invariant s) :
    s.settled := by
  rcases h with done | ⟨t,ht,_⟩
  · exact done
  · rw [empty] at ht
    exact (Finset.notMem_empty t ht).elim

theorem expired_witness :
    hasCut ({0,1} : Finset Nat) {1} ∧
    ¬ hasCut ({1} : Finset Nat) {1} := by
  constructor
  · exact ⟨0,by simp,by simp⟩
  · intro h
    rcases h with ⟨x,hx,hn⟩
    exact hn hx

-- This is the two-cut, no-third-slot local configuration. Moving both
-- missed cuts together is legal; either single target move is not.
theorem paired_only :
    hasCut (Finset.univ : Finset (Fin 2)) {0} ∧
    hasCut (Finset.univ : Finset (Fin 2)) {1} ∧
    ¬ hasCut (Finset.univ : Finset (Fin 2)) ({0,1} : Finset (Fin 2)) := by
  refine ⟨⟨1, by simp, by decide⟩, ⟨0, by simp, by decide⟩, ?_⟩
  rintro ⟨t, _, h⟩
  fin_cases t <;> simp at h

end ScopedLease
