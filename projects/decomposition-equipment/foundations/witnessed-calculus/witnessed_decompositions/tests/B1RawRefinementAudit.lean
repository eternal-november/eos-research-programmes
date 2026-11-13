import WitnessedDecompositions.RawRefinement
import WitnessedDecompositions.Examples

namespace WitnessedDecompositions.B1RawTests
open Tree Examples Examples.RepeatedComponent

/-- Same component, different source leaf occurrences, different inserted witnesses. -/
def leftInsert : Substitution pair := binaryChildren red (.leaf component)
def rightInsert : Substitution pair := binaryChildren (.leaf component) blue

def finishRight : Substitution (graft pair leftInsert)
  | .inl (.inl i) => nomatch i
  | .inl (.inr ()) => identity red
  | .inr () => blue

def finishLeft : Substitution (graft pair rightInsert)
  | .inl (.inl i) => nomatch i
  | .inl (.inr ()) => red
  | .inr () => identity blue

def firstLeft : Raw.Arrow pair (graft pair leftInsert) := ⟨leftInsert,rfl⟩
def firstRight : Raw.Arrow pair (graft pair rightInsert) := ⟨rightInsert,rfl⟩
def thenRight : Raw.Arrow (graft pair leftInsert) (graft pair differentReplacements) :=
  ⟨finishRight, by
    change Tree.node (S := signature) Witness.binary _ = Tree.node (S := signature) Witness.binary _
    congr 1
    funext i
    rcases i with (i | ⟨⟩) | ⟨⟩
    · exact nomatch i
    · exact graft_identity red
    · rfl⟩
def thenLeft : Raw.Arrow (graft pair rightInsert) (graft pair differentReplacements) :=
  ⟨finishLeft, by
    change Tree.node (S := signature) Witness.binary _ = Tree.node (S := signature) Witness.binary _
    congr 1
    funext i
    rcases i with (i | ⟨⟩) | ⟨⟩
    · exact nomatch i
    · rfl
    · exact graft_identity blue⟩

theorem independent_orders_same_arrow :
    Raw.comp firstLeft thenRight = Raw.comp firstRight thenLeft := Subsingleton.elim _ _

theorem independent_orders_recover_forest :
    (Raw.comp firstLeft thenRight).val = differentReplacements :=
  Tree.graft_injective pair (Raw.comp firstLeft thenRight).property

theorem swapped_labels_remain_distinct :
    graft pair differentReplacements ≠ graft pair swappedReplacements :=
  order_is_not_quotiented

/-- An existing primitive root cannot be rewritten as a different primitive root. -/
theorem cannot_refine_internal_vertex : ¬ Nonempty (Raw.Arrow red blue) := by
  rintro ⟨f⟩
  have h := congrArg Tree.generators f.property
  change Witness.red :: _ = Witness.blue :: _ at h
  have he := List.cons.inj h
  cases he.1

/-- A proper unary expansion cannot be undone (dependent event reversal). -/
theorem cannot_reverse_dependent_event : ¬ Nonempty (Raw.Arrow red (.leaf component)) := by
  rintro ⟨f⟩
  have h := congrArg Tree.generators f.property
  change Witness.red :: _ = [] at h
  cases h

/-- Nullary replacement consumes exactly its occurrence, leaving the other one. -/
def eraseArrow : Raw.Arrow pair (graft pair eraseFirst) := ⟨eraseFirst,rfl⟩

theorem nullary_remaining_occurrence : leaves (graft pair eraseArrow.val) = [component] := rfl

theorem nullary_has_unique_refinement : ∀ f g : Raw.Arrow nullary nullary, f = g :=
  fun _ _ => Subsingleton.elim _ _

#print axioms independent_orders_same_arrow
#print axioms independent_orders_recover_forest
#print axioms cannot_refine_internal_vertex
#print axioms cannot_reverse_dependent_event
#print axioms nullary_remaining_occurrence
end WitnessedDecompositions.B1RawTests
