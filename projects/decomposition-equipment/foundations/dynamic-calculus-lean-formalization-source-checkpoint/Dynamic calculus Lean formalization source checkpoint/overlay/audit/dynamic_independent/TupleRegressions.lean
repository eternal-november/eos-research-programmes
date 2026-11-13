import WitnessedDecompositions.Dynamic.Tuples

/- Independent concrete tests of actual states, event records, and nullary units. -/
namespace DynamicIndependent.Tuples
open WitnessedDecompositions
open WitnessedDecompositions.Dynamic

instance : Quiver Unit where Hom _ _ := Unit

def boolGraph : Graph where
  State := Bool
  Event := Bool
  source := id
  target := id

def boolFlip : Graph.Hom boolGraph boolGraph where
  state := Bool.not
  event := Bool.not
  source_comm _ := rfl
  target_comm _ := rfl

def boolAssignment : Assignment Unit where
  boundary _ := boolGraph
  component _ := boolGraph
  left _ := Graph.Hom.id _
  right _ := Graph.Hom.id _

def retainedNullary : boolAssignment.BoundaryMap
    (Quiver.Path.nil : Quiver.Path () ()) (Graph.Hom.id _) (Graph.Hom.id _) :=
  boolAssignment.assemble (Quiver.Path.nil : Quiver.Path () ()) (fun i => nomatch i) _ _ rfl

theorem empty_state_false : retainedNullary.val.state false = false := rfl
theorem empty_state_true : retainedNullary.val.state true = true := rfl
theorem empty_event_false : retainedNullary.val.event false = false := rfl
theorem empty_event_true : retainedNullary.val.event true = true := rfl

theorem empty_states_not_collapsed :
    retainedNullary.val.state false ≠ retainedNullary.val.state true := by change false ≠ true; decide

theorem empty_events_not_collapsed :
    retainedNullary.val.event false ≠ retainedNullary.val.event true := by change false ≠ true; decide

theorem retainedNullary_exact : Graph.IsIso retainedNullary.val := Graph.isIso_id _

theorem unequal_legs_have_no_nullary : ¬ Nonempty (boolAssignment.BoundaryMap
    (Quiver.Path.nil : Quiver.Path () ()) (Graph.Hom.id _) boolFlip) := by
  intro hn
  have h := (boolAssignment.nullary_nonempty_iff (Graph.Hom.id _) boolFlip).mp hn
  have hf := congrFun (congrArg Graph.Hom.state h) false
  change false = true at hf
  cases hf

def parallel : Graph where
  State := Unit
  Event := Bool
  source _ := ()
  target _ := ()

def terminal : Graph where
  State := Unit
  Event := Unit
  source _ := ()
  target _ := ()

def collapse : Graph.Hom parallel terminal where
  state _ := ()
  event _ := ()
  source_comm _ := rfl
  target_comm _ := rfl

def eventSwap : Graph.Hom parallel parallel where
  state := id
  event := Bool.not
  source_comm _ := rfl
  target_comm _ := rfl

theorem equal_state_maps : (Graph.Hom.id parallel).state = eventSwap.state := rfl

theorem actual_events_distinguish_maps : Graph.Hom.id parallel ≠ eventSwap := by
  intro h
  have hf := congrFun (congrArg Graph.Hom.event h) false
  change false = true at hf
  cases hf

def hiddenEventAssignment : Assignment Unit where
  boundary _ := terminal
  component _ := parallel
  left _ := collapse
  right _ := collapse

def hiddenEventNullary : hiddenEventAssignment.BoundaryMap
    (Quiver.Path.nil : Quiver.Path () ()) collapse collapse :=
  hiddenEventAssignment.assemble (Quiver.Path.nil : Quiver.Path () ()) (fun i => nomatch i) _ _ rfl

theorem state_bijection_alone_insufficient : Function.Bijective collapse.state := by
  constructor
  · intro a b _; cases a; cases b; rfl
  · intro a; exact ⟨(), rfl⟩

theorem event_collapse_not_iso : ¬ Graph.IsIso collapse := by
  rintro ⟨g, h, _⟩
  have h0 := congrFun (congrArg Graph.Hom.event h) false
  have h1 := congrFun (congrArg Graph.Hom.event h) true
  change g.event () = false at h0
  change g.event () = true at h1
  have hf : false = true := h0.symm.trans h1
  cases hf

theorem valid_unique_but_nonexact :
    Nonempty (hiddenEventAssignment.BoundaryMap
      (Quiver.Path.nil : Quiver.Path () ()) collapse collapse) ∧
    Subsingleton (hiddenEventAssignment.BoundaryMap
      (Quiver.Path.nil : Quiver.Path () ()) collapse collapse) ∧
    ¬ Graph.IsIso hiddenEventNullary.val :=
  ⟨⟨hiddenEventNullary⟩, hiddenEventAssignment.nullary_subsingleton (a := ()) collapse collapse,
    event_collapse_not_iso⟩

-- Arbitrary empty graphs remain available, rather than assuming all carriers inhabited.
def emptyGraph : Graph where
  State := Empty
  Event := Empty
  source := Empty.elim
  target := Empty.elim

theorem empty_graph_identity_exact : Graph.IsIso (Graph.Hom.id emptyGraph) :=
  Graph.isIso_id _

end DynamicIndependent.Tuples
