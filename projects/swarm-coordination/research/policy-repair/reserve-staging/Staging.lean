import Mathlib

namespace Staging

variable {V : Type} [PartialOrder V]
variable (h : V → Nat) (rank : ∀ {a b}, a < b → h a < h b)
variable (chain : ∀ {a b z : V}, a ≤ z → b ≤ z → a ≤ b ∨ b ≤ a)

def Top (A : Set V) (p : V) := p ∈ A ∧ ∀ z ∈ A, p ≤ z
def Conv (A : Set V) := ∀ {u v z : V}, u ∈ A → z ∈ A → u ≤ v → v ≤ z → v ∈ A

include rank chain in
lemma forced_mem {A B : Set V} {p q z : V} (pA : Top A p) (qB : Top B q)
    (hB : Conv B) (hqp : h q ≤ h p) (za : z ∈ A) (zb : z ∈ B) : p ∈ B := by
  have pz := pA.2 z za
  have qz := qB.2 z zb
  have qp : q ≤ p := by
    rcases chain pz qz with pq | qp
    · by_contra hnot
      have lt : p < q := lt_of_le_not_ge pq hnot
      exact (Nat.not_lt_of_ge hqp) (rank lt)
    · exact qp
  exact hB qB.1 zb qp pz

include rank chain in
theorem deepest_pair {I : Type} {B : I → Set V} {p : I → V} (j : I)
    (tops : ∀ i, Top (B i) (p i)) (conv : ∀ i, Conv (B i))
    (deep : ∀ i, h (p i) ≤ h (p j)) (i : I) (miss : p j ∉ B i) :
    Disjoint (B j) (B i) := by
  apply Set.disjoint_left.mpr
  intro z hj hi
  exact miss (forced_mem h rank chain (tops j) (tops i) (conv i) (deep i) hj hi)

omit [PartialOrder V] in
theorem component_cover {I J : Type} {B : I → Set V} {C : J → Set V}
    (bad : J → I) (obs : ∀ j, Disjoint (C j) (B (bad j))) :
    Disjoint (⋃ j, C j) (⋂ j, B (bad j)) := by
  apply Set.disjoint_left.mpr
  intro x hc hb
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hc
  exact Set.disjoint_left.mp (obs j) hj (Set.mem_iInter.mp hb j)

theorem isolated_star_tight {I : Type} (J : Set I) :
    (∃ k : I, ∀ i ∈ J, k ≠ i) ↔ J ≠ Set.univ := by
  constructor
  · rintro ⟨k, hk⟩ heq
    exact hk k (heq ▸ Set.mem_univ k) rfl
  · intro hm
    have notall : ¬ ∀ k : I, k ∈ J := by
      intro all
      exact hm (Set.eq_univ_of_forall all)
    push Not at notall
    obtain ⟨k, hk⟩ := notall
    exact ⟨k, fun i hi eq => hk (eq ▸ hi)⟩

end Staging
#print axioms Staging.forced_mem
#print axioms Staging.deepest_pair
#print axioms Staging.component_cover
#print axioms Staging.isolated_star_tight
