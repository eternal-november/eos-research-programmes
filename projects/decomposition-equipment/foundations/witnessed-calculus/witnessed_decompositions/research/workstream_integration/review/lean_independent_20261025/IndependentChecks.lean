import GraphForestNormalForms
import PublicExampleBridge

/- Reviewer-only adversarial probes. The finite idempotent monoid uses additive
notation: identity `one`, absorbing idempotent `absorb`. No cancellation axiom. -/
namespace IndependentIntegrationReview
open TypedNormalizer GraphCoordinates RewriteFragmentCandidate IntegrationGraphForest
inductive Idem where
  | one | absorb
  deriving DecidableEq

def iadd : Idem → Idem → Idem
  | .one, x => x
  | .absorb, _ => .absorb

instance : Zero Idem := ⟨.one⟩
instance : Add Idem := ⟨iadd⟩

instance : AddCommMonoid Idem where
  zero := .one
  add := iadd
  add_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  zero_add := by intro a; cases a <;> rfl
  add_zero := by intro a; cases a <;> rfl
  add_comm := by intro a b; cases a <;> cases b <;> rfl
  nsmul := nsmulRec

theorem genuinely_noncancellative :
    Idem.absorb + Idem.one = Idem.absorb + Idem.absorb ∧ Idem.one ≠ Idem.absorb := by
  decide

def e0 : Term Nat Idem 0 1 := .leaf (by decide) 0
def e1 : Term Nat Idem 1 1 := .leaf (by decide) 7
def e2 : Term Nat Idem 1 2 := .leaf (by decide) 9

def idemFourA : Term Nat Idem 0 2 :=
  .cut e0 (.cut (.deco .absorb e1) (.cut e1 e2))
def idemFourB : Term Nat Idem 0 2 :=
  .cut e0 (.cut (.deco .absorb e1) (.cut (.deco .absorb e1) e2))

theorem idem_four_mixed_equal_composites : E idemFourA idemFourB := by decide

theorem idem_local_tuple_entry_distinct : ¬ E e1 (.deco .absorb e1) := by decide

theorem idem_four_normal_form_sound :
    E idemFourA (reify idemFourA.normalize) ∧
    E idemFourB (reify idemFourB.normalize) :=
  ⟨term_equiv_reify_normalize _, term_equiv_reify_normalize _⟩

theorem idem_nullary_label_not_lost :
    ¬ E (.deco Idem.absorb (.unit 1) : Term Nat Idem 1 1) (.unit 1) := by decide

def interfaceA : Term Nat Idem 0 2 := .cut e0 e2
def interfaceB : Term Nat Idem 0 2 :=
  .cut (.leaf (by decide : (0 : Fin 3) ≤ 0) 0)
    (.leaf (by decide : (0 : Fin 3) ≤ 2) 9)

theorem same_blocks_not_full_arrow_profile :
    interfaceA.frontier.blocks = interfaceB.frontier.blocks ∧ ¬ E interfaceA interfaceB := by
  constructor
  · rfl
  · decide

def outside : CutTerm 1 1 := .leaf (by decide) {0}
def emptyExternal : CutTerm 1 1 := .leaf (by decide) ∅

theorem validity_hypothesis_essential :
    standardEvaluate sixGraph ∅ outside = standardEvaluate sixGraph ∅ emptyExternal ∧
    ¬ E outside emptyExternal ∧ ¬ Valid ∅ outside := by decide

theorem empty_external_not_nullary :
    ¬ E emptyExternal (.unit 1 : CutTerm 1 1) := by decide

theorem retained_whole_changes_full_witness :
    standardEvaluate sixGraph Finset.univ rightBare ≠
      standardEvaluate missingCrossEdge Finset.univ rightBare := by
  intro h
  exact different_retained_wholes (congrArg StandardCut.whole h)

theorem actual_ordered_forest_counterexample :
    E (rightBare.subst (frontierDispatch rightBare cancellingForest) 0)
      (rightBare.subst (frontierDispatch rightBare (identityForest rightBare)) 0) ∧
    forestNormal rightBare cancellingForest ≠ forestNormal rightBare (identityForest rightBare) :=
  equal_grafts_unequal_forest_codes

theorem actual_public_arrow_counterexample :
    WitnessedDecompositions.RefinementExamples.mixedLeftArrow ≠
      WitnessedDecompositions.RefinementExamples.mixedRightArrow :=
  WitnessedDecompositions.RefinementExamples.mixed_unequal_parallel_arrows

#print axioms genuinely_noncancellative
#print axioms idem_four_mixed_equal_composites
#print axioms idem_local_tuple_entry_distinct
#print axioms idem_four_normal_form_sound
#print axioms idem_nullary_label_not_lost
#print axioms same_blocks_not_full_arrow_profile
#print axioms validity_hypothesis_essential
#print axioms empty_external_not_nullary
#print axioms retained_whole_changes_full_witness
#print axioms actual_ordered_forest_counterexample
#print axioms actual_public_arrow_counterexample
end IndependentIntegrationReview
