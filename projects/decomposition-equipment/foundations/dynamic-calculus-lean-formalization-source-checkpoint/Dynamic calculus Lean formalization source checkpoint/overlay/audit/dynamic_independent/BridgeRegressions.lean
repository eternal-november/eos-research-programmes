import WitnessedDecompositions.Dynamic.Bridge
import audit.dynamic_independent.TargetRegressions

set_option backward.isDefEq.respectTransparency false
namespace DynamicIndependent.Bridge
open WitnessedDecompositions
open WitnessedDecompositions.Dynamic
open DynamicIndependent.Tuples
open DynamicIndependent.Target
open CategoryTheory

/- Two independent forests can agree after an outer map that sees only part of a component. -/
def resetEvent : Graph.Hom parallel parallel where
  state := id
  event _ := false
  source_comm _ := rfl
  target_comm _ := rfl

def partialRoot : D.Op color :=
  (D.operation twice (fun _ => resetEvent)
    ⟨⟨(collapse_precomp _).symm, collapse_precomp _⟩, collapse_precomp _⟩).val

def resetFirst (i : Path.Slot partialRoot.profile) :
    D.Op (Path.componentAt partialRoot.profile i) :=
  match i with
  | .inl (.inl e) => nomatch e
  | .inl (.inr ()) => unary resetEvent
  | .inr () => unary (Graph.Hom.id _)

def distinctForest : SemanticRefinement.Arrow D.calculus partialRoot partialRoot :=
  ⟨resetFirst, by
    apply Subtype.ext
    apply Assignment.MapOp.ext_word
    · rfl
    · rfl⟩

theorem equal_total_operation_does_not_erase_forest :
    SemanticRefinement.id (M := D.calculus) partialRoot ≠ distinctForest := by
  intro h
  have hf := congrArg (fun a : SemanticRefinement.Arrow D.calculus partialRoot partialRoot =>
    Assignment.MapOp.word (a.val (.inl (.inr ()))).val) h
  change [⟨color,Graph.Hom.id parallel⟩] =
    ([⟨color,resetEvent⟩] : List (Σ c, Graph.Hom parallel (D.component c))) at hf
  have hs := (List.cons.inj hf).1
  have hm : Graph.Hom.id parallel = resetEvent := eq_of_heq (Sigma.mk.inj_iff.mp hs).2
  have ht := congrFun (congrArg Graph.Hom.event hm) true
  change true = false at ht
  cases ht

/- A genuine, nonempty declared equation between syntactically different generators. -/
abbrev sig : Signature Unit where
  Generator := Bool
  source _ := ()
  target _ := ()
  input _ := color.edge.toPath
  output _ := color.edge

inductive declared : ∀ (c : Component Unit) (p : Quiver.Path c.source c.target),
    Tree.Operation (S := sig) c p → Tree.Operation (S := sig) c p → Prop where
  | identify : declared color color.edge.toPath
      (Tree.generatorOperation (S := sig) false) (Tree.generatorOperation (S := sig) true)

def goodAssignment : sig.Assignment D.calculus := fun _ => ⟨unary (Graph.Hom.id _), rfl⟩
def goodMaps : D.GeneratorMaps sig := D.generatorEquiv sig goodAssignment

theorem good_assignment_roundtrip : D.assignment sig goodMaps = goodAssignment :=
  (D.generatorEquiv sig).symm_apply_apply goodAssignment

theorem nonempty_equation_satisfied : D.EquationMaps sig declared goodMaps := by
  apply (D.equationMaps_iff_satisfies sig declared goodMaps).2
  rw [good_assignment_roundtrip]
  intro c p t u he
  cases he
  apply Subtype.ext
  change Tree.interpret D.calculus goodAssignment (Tree.corolla false) =
    Tree.interpret D.calculus goodAssignment (Tree.corolla true)
  simp only [Tree.interpret_corolla]
  rfl

theorem actual_original_free_extension :
    D.freeExtend sig goodMaps = Tree.extend D.calculus (D.assignment sig goodMaps) := rfl

theorem actual_original_presented_extension :
    D.presentedExtend sig declared goodMaps nonempty_equation_satisfied =
      Presentation.extend declared D.calculus
        (D.model sig declared goodMaps nonempty_equation_satisfied) := rfl

theorem actual_projection_factorization :
    (Presentation.projection declared).comp
      (D.presentedExtend sig declared goodMaps nonempty_equation_satisfied) =
        D.freeExtend sig goodMaps :=
  D.projection_presentedExtend sig declared goodMaps nonempty_equation_satisfied

theorem actual_original_refinement_functor :
    D.presentedRefinementFunctor sig declared goodMaps nonempty_equation_satisfied color =
      SemanticRefinement.functor
        (D.presentedExtend sig declared goodMaps nonempty_equation_satisfied) color := rfl

def badAssignment : sig.Assignment D.calculus := fun b =>
  ⟨unary (if (b : Bool) then eventSwap else Graph.Hom.id _), rfl⟩
def badMaps : D.GeneratorMaps sig := D.generatorEquiv sig badAssignment

theorem bad_assignment_roundtrip : D.assignment sig badMaps = badAssignment :=
  (D.generatorEquiv sig).symm_apply_apply badAssignment

-- Both generator maps have the same state function, but the event equation fails.
theorem event_permutation_equation_rejected : ¬ D.EquationMaps sig declared badMaps := by
  intro h
  have hs := (D.equationMaps_iff_satisfies sig declared badMaps).1 h
  rw [bad_assignment_roundtrip] at hs
  have he := hs _ _ _ _ declared.identify
  have hv := congrArg Subtype.val he
  change Tree.interpret D.calculus badAssignment (Tree.corolla false) =
    Tree.interpret D.calculus badAssignment (Tree.corolla true) at hv
  simp only [Tree.interpret_corolla] at hv
  exact identity_and_swap_operations_differ hv

theorem no_descent_from_equal_states_alone :
    ¬ ∃ F : Calc.Hom (Presentation.quotient declared) D.calculus,
      (Presentation.projection declared).comp F = D.freeExtend sig badMaps := by
  intro h
  exact event_permutation_equation_rejected ((D.descends_iff sig declared badMaps).1 h)

end DynamicIndependent.Bridge
