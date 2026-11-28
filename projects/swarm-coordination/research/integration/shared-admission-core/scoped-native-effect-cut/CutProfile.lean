namespace CutProfile

inductive Act where | inspect | effect
  deriving DecidableEq, Repr
inductive Outcome where | past | absent | wrongScope | noWitness | busy | missingService | enable
  deriving DecidableEq, Repr
structure P where
  act : Act
  scope : Bool
  value : Bool
  room : Bool
  service : Bool
  deriving DecidableEq, Repr

def check (p : P) : Outcome :=
  if !p.scope then .wrongScope
  else match p.act with
  | .inspect => if p.value then .past else .absent
  | .effect =>
    if !p.value then .noWitness
    else if !p.room then .busy
    else if !p.service then .missingService
    else .enable

def comparison (a b : P) : Prop :=
  a.act = b.act ∧ a.scope = b.scope ∧ a.value = b.value ∧
    (a.act = .inspect ∨ (a.room = b.room ∧ a.service = b.service))
def mask (p : P) (s v r n : Bool) : P :=
  {p with scope := p.scope || s, value := p.value || v,
          room := p.room || r, service := p.service || n}
def signature (p : P) :=
  (p.act, check (mask p false true true true), check (mask p true false true true),
    check (mask p true true false true), check (mask p true true true false))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1500000 in
theorem exact_for_isolating_tests (a b : P) : comparison a b ↔ signature a = signature b := by
  obtain ⟨aa, as, av, ar, an⟩ := a
  obtain ⟨ba, bs, bv, br, bn⟩ := b
  cases aa <;> cases ba <;> cases as <;> cases av <;> cases ar <;> cases an <;>
  cases bs <;> cases bv <;> cases br <;> cases bn <;>
    simp [comparison, signature, mask, check]

theorem push_comparison (a b : P) (s v r n : Bool) (h : comparison a b) :
    comparison (mask a s v r n) (mask b s v r n) := by
  rcases h with ⟨ha, hs, hv, i | ⟨hr, hn⟩⟩
  · exact ⟨ha, by simp [mask,hs], by simp [mask,hv], Or.inl i⟩
  · exact ⟨ha, by simp [mask,hs], by simp [mask,hv],
      Or.inr ⟨by simp [mask,hr], by simp [mask,hn]⟩⟩

theorem preserves_decision (a b : P) (h : comparison a b) : check a = check b := by
  rcases h with ⟨ha, hs, hv, i | ⟨hr, hn⟩⟩
  · have j : b.act = .inspect := ha.symm.trans i
    simp [check,i,j,hs,hv]
  · simp [check,ha,hs,hv,hr,hn]

theorem cross_all_declared_restorations (a b : P) (h : comparison a b) (s v r n : Bool) :
    check (mask a s v r n) = check (mask b s v r n) :=
  preserves_decision _ _ (push_comparison a b s v r n h)

theorem exact_full_test_family (a b : P) :
    comparison a b ↔ a.act = b.act ∧
      ∀ s v r n : Bool, check (mask a s v r n) = check (mask b s v r n) := by
  constructor
  · intro h
    exact ⟨h.1, cross_all_declared_restorations _ _ h⟩
  · rintro ⟨same, tests⟩
    apply (exact_for_isolating_tests a b).2
    unfold signature
    rw [same, tests false true true true, tests true false true true,
      tests true true false true, tests true true true false]

end CutProfile
