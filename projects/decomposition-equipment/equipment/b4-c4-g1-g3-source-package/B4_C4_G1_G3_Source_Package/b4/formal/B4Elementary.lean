import WitnessedDecompositions.RawRefinement
import WitnessedDecompositions.WeightInvariant
open WitnessedDecompositions
namespace B4
universe u v w
variable {V : Type u} [Quiver.{v} V] {S : Signature.{u,v,w} V}
/-- Inserting primitives of nonnegative weight cannot decrease total weight. -/
theorem weight_monotone (w : S.Generator → Nat) {c : Component V}
    (t : Tree S c) (f : (Tree.collection S).Family (Tree.frontier t)) :
    Tree.weight w t ≤ Tree.weight w (Tree.profileGraft t f) := by
  rw [Tree.weight_profileGraft]
  exact Nat.le_add_right _ _
/-- Positive added weight strictly increases the invariant, including nullaries. -/
theorem weight_strict (w : S.Generator → Nat) {c : Component V}
    (t : Tree S c) (f : (Tree.collection S).Family (Tree.frontier t))
    (h : 0 < Path.sum (Tree.frontier t) (fun i => Tree.weight w (f i))) :
    Tree.weight w t < Tree.weight w (Tree.profileGraft t f) := by
  rw [Tree.weight_profileGraft]
  exact Nat.lt_add_of_pos_right h
#print axioms weight_monotone
#print axioms weight_strict
end B4
#print axioms Tree.graft_injective
#print axioms Tree.graft_no_cycle
#print axioms Tree.graftLeafEquiv
#print axioms Tree.graftLeafEquiv_component
#print axioms Tree.collect_graftLeaf
#print axioms Tree.collect_profileGraftLeaf
#print axioms Tree.frontier_profileGraft
#print axioms Tree.weight_profileGraft
#print axioms Tree.weight_substituteOperation
#print axioms Presentation.derives_weight
#print axioms Raw.antisymm
