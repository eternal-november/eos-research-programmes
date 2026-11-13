import WitnessedDecompositions.Dynamic.Target
import audit.dynamic_independent.TupleRegressions

/- Independent adversarial tests of the actual target calculus, not just its profile API. -/
namespace DynamicIndependent.Target
open WitnessedDecompositions
open WitnessedDecompositions.Dynamic
open DynamicIndependent.Tuples

abbrev D := hiddenEventAssignment

def color : Component Unit := ⟨(), (), ()⟩
def twice : Quiver.Path () () := color.edge.toPath.cons color.edge

theorem collapse_precomp (m : Graph.Hom parallel parallel) : m.comp collapse = collapse := by
  apply Graph.Hom.ext <;> funext x <;> rfl

def unary (m : Graph.Hom parallel parallel) : D.Op color :=
  (D.operation color.edge.toPath (fun i => match i with
    | .inl e => nomatch e
    | .inr () => m) ⟨(collapse_precomp m).symm, collapse_precomp m⟩).val

def duplicate : D.Op color :=
  (D.operation twice (fun _ => Graph.Hom.id _) ⟨⟨rfl,rfl⟩,rfl⟩).val

def independentReplacement (i : Path.Slot duplicate.profile) :
    D.Op (Path.componentAt duplicate.profile i) :=
  match i with
  | .inl (.inl e) => nomatch e
  | .inl (.inr ()) => unary eventSwap
  | .inr () => unary (Graph.Hom.id _)

def substituted := Assignment.Op.subst duplicate independentReplacement

theorem first_record_flipped :
    (substituted.maps (.inl (.inr ()))).event false = true := rfl

theorem second_record_retained :
    (substituted.maps (.inr ())).event false = false := rfl

theorem different_repeated_occurrences :
    (substituted.maps (.inl (.inr ()))).event false ≠
      (substituted.maps (.inr ())).event false := by change true ≠ false; decide

theorem identity_and_swap_operations_differ :
    unary (Graph.Hom.id _) ≠ unary eventSwap := by
  intro h
  have hm := congrArg (fun a : D.Op color =>
    Assignment.MapOp.word a.val) h
  have hh : [⟨color, Graph.Hom.id parallel⟩] =
      ([⟨color,eventSwap⟩] : List (Σ c, Graph.Hom parallel (D.component c))) := hm
  have heq := (List.cons.inj hh).1
  have hmaps : Graph.Hom.id parallel = eventSwap := by
    exact eq_of_heq (Sigma.mk.inj_iff.mp heq).2
  exact actual_events_distinguish_maps hmaps

-- The original Calc laws apply to this concrete nonexact dynamic operation.
theorem actual_calc_right_unit :
    D.calculus.subst duplicate (D.calculus.identityFamily duplicate.profile) = duplicate :=
  D.calculus.subst_identity duplicate

theorem actual_calc_associative
    (h : D.calculus.toCollection.Family (D.calculus.profile
      (D.calculus.subst duplicate independentReplacement))) :
    D.calculus.subst (D.calculus.subst duplicate independentReplacement) h =
      D.calculus.subst duplicate
        (D.calculus.composeFamily duplicate independentReplacement h) :=
  D.calculus.subst_assoc duplicate independentReplacement h

-- All empty replacement branches must preserve a nonterminal boundary, not return Unit.
def boolDuplicate : boolAssignment.Op color :=
  (boolAssignment.operation twice (fun _ => Graph.Hom.id _) ⟨⟨rfl,rfl⟩,rfl⟩).val

def boolErase (c : Component Unit) : boolAssignment.Op c := by
  rcases c with ⟨s,t,e⟩
  cases s; cases t
  exact (boolAssignment.operation (c := ⟨(),(),e⟩) (Quiver.Path.nil : Quiver.Path () ())
    (fun i => nomatch i) rfl).val

def allNullary := Assignment.Op.subst boolDuplicate
  (fun i => boolErase (Path.componentAt boolDuplicate.profile i))

theorem all_nullary_profile_is_nil : allNullary.profile = Quiver.Path.nil := rfl

theorem all_nullary_retains_state (b : Bool) : allNullary.witness.val.state b = b := rfl

theorem all_nullary_retains_event (b : Bool) : allNullary.witness.val.event b = b := rfl

theorem all_nullary_retains_distinct_records :
    allNullary.witness.val.event false ≠ allNullary.witness.val.event true := by
  change false ≠ true
  decide

-- Nonexact operations are admitted, rather than imposing exactness on the target.
def actualNonexactNullary : D.calculus.Operation color .nil :=
  D.operation .nil (fun i => nomatch i) rfl

theorem target_contains_nonexact_nullary : ¬ actualNonexactNullary.val.Exact :=
  event_collapse_not_iso

end DynamicIndependent.Target
