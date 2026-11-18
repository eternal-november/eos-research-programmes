import RankedJobs

/-! Material accounting for one commissioned work unit. The bin entries are
cumulative physical receipts of this unit, indexed by the load in the proof.
An idle event also represents an attempted stroke against an empty pocket. -/
namespace Carrier

structure Mark where
  pocket : Nat
  chuteP : Nat
  chuteQ : Nat
  binP : Nat
  binQ : Nat

inductive Event where
  | idle | releaseP | releaseQ | landP | landQ

def initial : Mark := ⟨1, 0, 0, 0, 0⟩

def mass (m : Mark) := m.pocket + m.chuteP + m.chuteQ + m.binP + m.binQ

def step (m : Mark) : Event → Mark
  | .idle => m
  | .releaseP => if m.pocket = 0 then m else
      {m with pocket := m.pocket - 1, chuteP := m.chuteP + 1}
  | .releaseQ => if m.pocket = 0 then m else
      {m with pocket := m.pocket - 1, chuteQ := m.chuteQ + 1}
  | .landP => if m.chuteP = 0 then m else
      {m with chuteP := m.chuteP - 1, binP := m.binP + 1}
  | .landQ => if m.chuteQ = 0 then m else
      {m with chuteQ := m.chuteQ - 1, binQ := m.binQ + 1}

theorem step_mass (m : Mark) (e : Event) : mass (step m e) = mass m := by
  cases e <;> simp only [step]
  all_goals first | rfl | (split <;> simp [mass] <;> omega)

theorem word_mass (es : List Event) (m : Mark) : mass (es.foldl step m) = mass m := by
  induction es generalizing m with
  | nil => rfl
  | cons e es ih => exact (ih (step m e)).trans (step_mass m e)

theorem settled (es : List Event) (m : Mark) (atEnd : m = es.foldl step initial)
    (empty : m.pocket + m.chuteP + m.chuteQ = 0) :
    (m.binP = 1 ∧ m.binQ = 0) ∨ (m.binP = 0 ∧ m.binQ = 1) := by
  have h : mass m = 1 := atEnd ▸ word_mass es initial
  unfold mass at h
  omega

theorem frame {I : Type} (a : I) (before after : I → Mark) (e : Event)
    (target : after a = step (before a) e)
    (other : ∀ i, i ≠ a → after i = before i)
    (old : ∀ i, mass (before i) = 1) : ∀ i, mass (after i) = 1 :=
  PortabilityJobs.local_rules_assemble (fun i f => mass (f i) = 1)
    (fun i => i = a) (fun i => i = a) before after old
    (by intro i eq reads; subst i; rw [target, step_mass]; exact reads a rfl)
    (by intro i different h; rwa [other i different])

#print axioms word_mass
#print axioms settled
#print axioms frame

end Carrier
