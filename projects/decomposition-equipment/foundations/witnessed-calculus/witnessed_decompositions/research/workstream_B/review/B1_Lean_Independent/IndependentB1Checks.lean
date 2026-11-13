import WitnessedDecompositions.RawRefinement
import WitnessedDecompositions.Examples

open WitnessedDecompositions
namespace IndependentB1Checks
universe u v w z
variable {V : Type u} [Quiver.{v} V] {S : Signature.{u,v,w} V}

-- A no-leaf source, including any arbitrary closed tree, has precisely its
-- identity forest; this is not a positivity or leaf-count argument.
theorem closed_forest_unique {c : Component V} (t : Tree S c)
    (closed : IsEmpty (Tree.Leaf t)) (σ : Tree.Substitution t) :
    σ = Tree.identity t := by
  apply (Tree.substitutionEquiv t).injective
  funext l
  exact (closed.false l).elim

theorem closed_arrows_fix_target {c : Component V} {t u : Tree S c}
    (closed : IsEmpty (Tree.Leaf t)) (f : Raw.Arrow t u) : u = t := by
  rw [← f.property, closed_forest_unique t closed f.val, Tree.graft_identity]

-- This is an actual ordered list of occurrence identities. Neither labels nor
-- counts could distinguish the permutations this test can distinguish.
theorem occurrence_identity_traversal {c : Component V} (t : Tree S c)
    (σ : Tree.Substitution t) :
    Path.collect (Tree.frontier (Tree.graft t σ))
      (fun i => [Tree.frontierLeafEquiv (Tree.graft t σ) i]) =
      Tree.collectLeaves t (fun l => Tree.collectLeaves (Tree.atLeaf t σ l)
        (fun k => [Tree.graftLeaf t σ l k])) :=
  Tree.collect_profileGraftLeaf t σ (fun k => [k])

-- The reindexing used by the three-layer theorem cannot discard or relabel
-- the third coordinate: its value is heterogeneously equal to the input.
theorem innerLeaf_preserves_occurrence {c : Component V} (t : Tree S c)
    (σ : Tree.Substitution t) (τ : Tree.Substitution (Tree.graft t σ))
    (l : Tree.Leaf t) (k : Tree.Leaf (Tree.atLeaf t σ l))
    (m : Tree.Leaf (Tree.atLeaf (Tree.atLeaf t σ l) (Tree.innerAtLeaf t σ τ l) k)) :
    HEq (Tree.innerLeaf t σ τ l k m) m := by
  induction t with
  | leaf c => rfl
  | node g ch ih => exact ih l.1 (σ l.1) (τ l.1) l.2 k m

section Nullary
open Tree Examples Examples.RepeatedComponent
example {t : Tree signature component} (f : Raw.Arrow nullary t) : t = nullary :=
  closed_arrows_fix_target nullary_has_no_occurrences f

-- Equal output labels do not license swapping actual occurrence positions.
example : differentReplacements ≠ swappedReplacements := by
  intro h
  exact order_is_not_quotiented (congrArg (graft pair) h)

-- The nullary block has no hidden survivor. The unique surviving final leaf
-- is mapped to the original right occurrence, not the deleted left occurrence.
def survivingLeaf : Leaf (graft pair eraseFirst) :=
  ⟨Sum.inr (), ⟨Sum.inr (), ()⟩⟩
example : (graftLeafEquiv pair eraseFirst survivingLeaf).1 = ⟨Sum.inr (), ()⟩ := rfl
example : leafComponent (graft pair eraseFirst) survivingLeaf = component := rfl
end Nullary

#print axioms closed_forest_unique
#print axioms closed_arrows_fix_target
#print axioms occurrence_identity_traversal
#print axioms innerLeaf_preserves_occurrence
end IndependentB1Checks
