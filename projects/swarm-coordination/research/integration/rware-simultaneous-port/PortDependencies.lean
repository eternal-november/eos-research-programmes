import Mathlib

namespace PortDependencies
variable {V : Type}

def Closed (edge : V → V → Prop) (S : Set V) :=
  ∀ ⦃i j⦄, i ∈ S → edge i j → j ∈ S

def Support (edge : V → V → Prop) (i : V) :=
  {j | Relation.ReflTransGen edge i j}

lemma support_closed (edge : V → V → Prop) (i : V) : Closed edge (Support edge i) := by
  intro u v hu huv
  exact Relation.ReflTransGen.tail hu huv

lemma support_min (edge : V → V → Prop) {S : Set V}
    (cl : Closed edge S) {i : V} (hi : i ∈ S) : Support edge i ⊆ S := by
  intro j hj
  change Relation.ReflTransGen edge i j at hj
  induction hj with
  | refl => exact hi
  | tail _ e ih => exact cl ih e

theorem exact_effect (edge : V → V → Prop) (allowed : Set V) (i : V) :
    (∃ S : Set V, Closed edge S ∧ S ⊆ allowed ∧ i ∈ S) ↔ Support edge i ⊆ allowed := by
  constructor
  · rintro ⟨S, cl, ok, hi⟩
    exact (support_min edge cl hi).trans ok
  · intro ok
    exact ⟨_, support_closed edge i, ok, Relation.ReflTransGen.refl⟩

theorem same_on_support (edge : V → V → Prop) (i : V) (A B : Set V)
    (same : ∀ j ∈ Support edge i, j ∈ A ↔ j ∈ B) :
    (∃ S : Set V, Closed edge S ∧ S ⊆ A ∧ i ∈ S) ↔
    (∃ S : Set V, Closed edge S ∧ S ⊆ B ∧ i ∈ S) := by
  rw [exact_effect, exact_effect]
  exact ⟨fun a _ h => (same _ h).mp (a h), fun b _ h => (same _ h).mpr (b h)⟩

end PortDependencies
#print axioms PortDependencies.support_closed
#print axioms PortDependencies.support_min
#print axioms PortDependencies.exact_effect
#print axioms PortDependencies.same_on_support
