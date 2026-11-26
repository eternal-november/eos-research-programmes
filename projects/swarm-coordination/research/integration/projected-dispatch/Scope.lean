import Mathlib

namespace QueueScope
variable {ι : Type*}
def safePrefixSet (missing : ι → Prop) (edge : ι → ι → Prop)
    (exec : ι → Prop) : Prop :=
  (∀ x, missing x → ¬ exec x) ∧
  (∀ x y, edge x y → exec y → exec x)

def forcedHold (missing : ι → Prop) (edge : ι → ι → Prop) (y : ι) : Prop :=
  ∃ x, missing x ∧ Relation.ReflTransGen edge x y

theorem legal_complement (missing : ι → Prop) (edge : ι → ι → Prop) :
    safePrefixSet missing edge (fun i => ¬ forcedHold missing edge i) := by
  constructor
  · intro x hx h
    exact h ⟨x, hx, Relation.ReflTransGen.refl⟩
  · intro x y e hy hx
    obtain ⟨z, hz, path⟩ := hx
    exact hy ⟨z, hz, path.tail e⟩

theorem maximal_complement (missing : ι → Prop) (edge : ι → ι → Prop)
    (exec : ι → Prop) (valid : safePrefixSet missing edge exec) (y : ι) :
    exec y → ¬ forcedHold missing edge y := by
  intro hy hold
  obtain ⟨x, hx, path⟩ := hold
  apply valid.1 x hx
  induction path with
  | refl => exact hy
  | tail p step ih => exact ih (valid.2 _ _ step hy)
end QueueScope

#print axioms QueueScope.legal_complement
#print axioms QueueScope.maximal_complement
