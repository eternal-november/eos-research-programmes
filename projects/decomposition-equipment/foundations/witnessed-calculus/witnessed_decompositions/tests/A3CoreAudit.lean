import WitnessedDecompositions.PresentationExamples

namespace WorkstreamAReview.A3
open WitnessedDecompositions
open WitnessedDecompositions.PresentationExamples.Mixed
open WitnessedDecompositions.Examples.MultiInterface (whole)

/-- Deliberately lossy semantics, used only as a negative control: every
operation with the same FULL typed profile has the same image. -/
def profileOnly : ParallelCongruence (Tree.freeCalc S) where
  Rel t u := Tree.frontier t = Tree.frontier u
  refl _ := rfl
  symm := Eq.symm
  trans := Eq.trans
  parallel h := h
  substitute a b _ q f g _ :=
    (Tree.substituteOperation a q f).property.trans
      (Tree.substituteOperation b q g).property.symm

noncomputable def lossyAssignment : S.Assignment profileOnly.quotient :=
  Tree.restrict profileOnly.quotient profileOnly.projection

theorem lossy_model_satisfies :
    Presentation.Satisfies equations profileOnly.quotient lossyAssignment := by
  intro c p t u _
  apply Subtype.ext
  change Tree.interpret _ lossyAssignment t.val = Tree.interpret _ lossyAssignment u.val
  simp only [lossyAssignment, Presentation.interpret_restrict]
  exact (profileOnly.quotient_eq_iff t.val u.val).2
    (t.property.trans u.property.symm)

theorem equal_in_one_model_but_not_derivable :
    Tree.interpret profileOnly.quotient lossyAssignment red =
      Tree.interpret profileOnly.quotient lossyAssignment blue ∧
    ¬ Presentation.Derives S equations red blue := by
  constructor
  · simp only [lossyAssignment, Presentation.interpret_restrict]
    exact (profileOnly.quotient_eq_iff red blue).2 undeclared_is_parallel
  · exact undeclared_not_derivable

/-- Mutation control: adding the formerly absent equation actually changes
the generated relation. This is not a mutation of the accepted presentation. -/
inductive ExtraDeclared : ∀ (c : Component Nat) (p : Quiver.Path c.source c.target),
    Tree.Operation (S := S) c p → Tree.Operation (S := S) c p → Prop where
  | inherited {c p} {t u} : equations c p t u → ExtraDeclared c p t u
  | merge : ExtraDeclared whole (S.input Gen.red)
      (Tree.generatorOperation (S := S) Gen.red)
      (Tree.generatorOperation (S := S) Gen.blue)

theorem extra_equation_changes_derivability :
    Presentation.Derives S ExtraDeclared red blue :=
  Presentation.Derives.equation _ _ ExtraDeclared.merge

#print axioms Presentation.derives_least
#print axioms ParallelCongruence.quotientSubstitute_project
#print axioms ParallelCongruence.projection_substitute_eq_of_rel
#print axioms ParallelCongruence.quotient_subst_assoc
#print axioms ParallelCongruence.quotient_substitute_eq
#print axioms ParallelCongruence.factor_unique
#print axioms ParallelCongruence.quotientMap_comp
#print axioms Presentation.homEquiv
#print axioms Presentation.extend_natural
#print axioms Presentation.derives_iff_all_models
#print axioms PresentationExamples.Mixed.statistic_satisfies
#print axioms PresentationExamples.Mixed.statistic_separates
#print axioms PresentationExamples.Nullary.quotient_preserves_nullary_insertion
#print axioms equal_in_one_model_but_not_derivable
#print axioms extra_equation_changes_derivability

end WorkstreamAReview.A3
