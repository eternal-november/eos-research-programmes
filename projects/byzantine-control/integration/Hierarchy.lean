import Std

/- Small transport facts for the finite causal-game compiler. The distributed
   synthesis theorem is imported from the primary source, not assumed as an axiom. -/
namespace ByzantineHierarchy

theorem common_observations_same_information
    (view : I → H → O) (publicView : H → O)
    (same : ∀ i h, view i h = publicView h) (i j : I) (h k : H) :
    (view i h = view i k) ↔ (view j h = view j k) := by
  simp only [same]

theorem refinement_orders_information
    (fine : H → A) (coarse : H → B) (decode : A → B)
    (factor : ∀ h, decode (fine h) = coarse h) (h k : H)
    (equal : fine h = fine k) : coarse h = coarse k := by
  rw [← factor h, ← factor k, equal]

/- Retaining a hidden incoming whole profile prevents different edge labels
   witnessing the component strategies separately. -/
theorem unique_incoming_profile_couples
    (Edge : (I → A) → Prop) (stored wanted : I → A)
    (existsEdge : ∃ a, Edge a)
    (unique : ∀ a, Edge a → a = stored) :
    (∀ i, ∃ a, Edge a ∧ a i = wanted i) ↔ Edge wanted := by
  constructor
  · intro each
    have equal : stored = wanted := by
      funext i
      obtain ⟨a,ha,hi⟩ := each i
      rw [unique a ha] at hi
      exact hi
    obtain ⟨a,ha⟩ := existsEdge
    rw [unique a ha, equal] at ha
    exact ha
  · intro h i
    exact ⟨wanted,h,rfl⟩

def compiledMemory (output : M → O → A) (update : M → O → A → M)
    (initial : M) (observations : Nat → O) : Nat → M
  | 0 => initial
  | t+1 => let m := compiledMemory output update initial observations t
           update m (observations t) (output m (observations t))

/- A deterministic actor's issued action is reconstructible from its observation
   stream and its own policy. This is a policy-relative statement. -/
theorem own_action_memory_transport
    (output : M → O → A) (update : M → O → A → M)
    (initial : M) (observations : Nat → O) (memory : Nat → M) (issued : Nat → A)
    (start : memory 0 = initial)
    (commands : ∀ t, issued t = output (memory t) (observations t))
    (steps : ∀ t, memory (t+1) = update (memory t) (observations t) (issued t)) :
    ∀ t, memory t = compiledMemory output update initial observations t := by
  intro t
  induction t with
  | zero => exact start
  | succ t ih => rw [steps t, commands t, ih]; rfl

theorem own_action_command_transport
    (output : M → O → A) (update : M → O → A → M)
    (initial : M) (observations : Nat → O) (memory : Nat → M) (issued : Nat → A)
    (start : memory 0 = initial)
    (commands : ∀ t, issued t = output (memory t) (observations t))
    (steps : ∀ t, memory (t+1) = update (memory t) (observations t) (issued t)) :
    ∀ t, issued t = output (compiledMemory output update initial observations t) (observations t) := by
  intro t
  rw [commands t, own_action_memory_transport output update initial observations memory issued start commands steps t]

#print axioms common_observations_same_information
#print axioms refinement_orders_information
#print axioms unique_incoming_profile_couples
#print axioms own_action_memory_transport
#print axioms own_action_command_transport
end ByzantineHierarchy
