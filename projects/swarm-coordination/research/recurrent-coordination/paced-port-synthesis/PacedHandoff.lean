import Lean

namespace PacedHandoff

def compose {X : Type} (a b : X → X → Prop) (u v : X) : Prop :=
  ∃ t, a u t ∧ b t v

theorem assoc {X : Type} (a b c : X → X → Prop) (u v : X) :
    compose (compose a b) c u v ↔ compose a (compose b c) u v := by
  constructor
  · rintro ⟨j, ⟨i, hi, hij⟩, hj⟩
    exact ⟨i, hi, j, hij, hj⟩
  · rintro ⟨i, hi, j, hij, hj⟩
    exact ⟨j, ⟨i, hi, hij⟩, hj⟩

def overlaps (a b len : Nat) : Prop := a < b+len ∧ b < a+len

theorem paced_conflict (base P g : Nat) (hg : 0 < g) (hp : g ≤ P) :
    overlaps (base+g) (base+P) g ↔ P < 2*g := by
  unfold overlaps
  omega

theorem saturating_before_handoff (base P g : Nat) (hg : 0 < g) :
    overlaps base (base+P) g ↔ P < g := by
  unfold overlaps
  omega

#print axioms assoc
#print axioms paced_conflict
#print axioms saturating_before_handoff
end PacedHandoff
