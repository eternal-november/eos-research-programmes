import Lean
namespace AuthorityCut

def issue (t revoke : Nat) := t < revoke
def through (t duration revoke : Nat) := t + duration < revoke

theorem through_implies_issue (t duration revoke : Nat) :
    through t duration revoke → issue t revoke := by
  unfold through issue
  omega

theorem exact_gap (t duration revoke : Nat) :
    issue t revoke ∧ ¬ through t duration revoke ↔
      t < revoke ∧ revoke ≤ t+duration := by
  unfold issue through
  omega

theorem no_retroactive_geometry {R : Type} (grant old new : R)
    (q : grant = old) (changed : old ≠ new) : grant ≠ new := by
  intro neq
  exact changed (q.symm.trans neq)

theorem observation_alias_blocks {O A : Type} {o₁ o₂ : O}
    (same : o₁ = o₂) (l r : A → Prop)
    (incompatible : ∀ a, l a → r a → False) :
    ¬ ∃ policy : O → A, l (policy o₁) ∧ r (policy o₂) := by
  rintro ⟨p, hl, hr⟩
  subst o₂
  exact incompatible (p o₁) hl hr

#print axioms through_implies_issue
#print axioms exact_gap
#print axioms no_retroactive_geometry
#print axioms observation_alias_blocks
end AuthorityCut
