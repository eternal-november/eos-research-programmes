module
public import WitnessedDecompositions.FreeCalculus
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v z z'
namespace WitnessedDecompositions.Dynamic
open Path
variable {V : Type u} [Quiver.{v} V]

/-- Assemble an independently indexed family using the original expansion bijection. -/
def joinFamily (F : Component V → Type z) {a b : V} (p : Quiver.Path a b)
    (q : ∀ i : Slot p, Quiver.Path (componentAt p i).source (componentAt p i).target)
    (f : ∀ i : Slot p, ∀ j : Slot (q i), F (componentAt (q i) j))
    (k : Slot (expand p q)) : F (componentAt (expand p q) k) :=
  occurrenceTransport F (componentAt_slotExpand p q k).symm
    (f (slotExpand p q k).1 (slotExpand p q k).2)

@[simp] theorem expandFamily_joinFamily (F : Component V → Type z) {a b : V}
    (p : Quiver.Path a b)
    (q : ∀ i : Slot p, Quiver.Path (componentAt p i).source (componentAt p i).target)
    (f : ∀ i : Slot p, ∀ j : Slot (q i), F (componentAt (q i) j))
    (i : Slot p) (j : Slot (q i)) :
    expandFamily F p q (joinFamily F p q f) i j = f i j := by
  apply eq_of_heq
  unfold expandFamily joinFamily
  apply (Tree.occurrenceTransport_heq F _ _).trans
  apply (Tree.occurrenceTransport_heq F _ _).trans
  exact Tree.dependent_apply_heq (fun ij : Σ i, Slot (q i) => f ij.1 ij.2)
    ((slotExpand p q).apply_symm_apply ⟨i,j⟩)

@[simp] theorem joinFamily_expandFamily (F : Component V → Type z) {a b : V}
    (p : Quiver.Path a b)
    (q : ∀ i : Slot p, Quiver.Path (componentAt p i).source (componentAt p i).target)
    (f : ∀ i : Slot (expand p q), F (componentAt (expand p q) i)) :
    joinFamily F p q (expandFamily F p q f) = f := by
  funext k
  apply eq_of_heq
  unfold joinFamily expandFamily
  apply (Tree.occurrenceTransport_heq F _ _).trans
  apply (Tree.occurrenceTransport_heq F _ _).trans
  exact Tree.dependent_apply_heq f ((slotExpand p q).symm_apply_apply k)

/-- Extensionality tests every occurrence, without identifying repeated colors. -/
theorem expandFamily_injective (F : Component V → Type z) {a b : V}
    (p : Quiver.Path a b)
    (q : ∀ i : Slot p, Quiver.Path (componentAt p i).source (componentAt p i).target) :
    Function.Injective (expandFamily F p q) := by
  intro f g h
  have := congrArg (joinFamily F p q) h
  simpa only [joinFamily_expandFamily] using this

/-- Forgetting transports into a dependent pair loses no family data. -/
theorem sigma_transport (F : Component V → Type z) {c d : Component V}
    (e : c = d) (x : F c) :
    (⟨d, occurrenceTransport F e x⟩ : Sigma F) = ⟨c,x⟩ := by cases e; rfl

/-- Ordered, fully typed coordinates; used only for extensional proofs. -/
def word (F : Component V → Type z) {a b : V} (p : Quiver.Path a b)
    (f : ∀ i : Slot p, F (componentAt p i)) : List (Sigma F) :=
  collect p (fun i => [⟨componentAt p i, f i⟩])

theorem word_injective (F : Component V → Type z) {a b : V}
    (p : Quiver.Path a b) : Function.Injective (word F p) := by
  intro f g h
  have h' := collect_singleton_injective p h
  funext i
  have hi := congrFun h' i
  exact eq_of_heq (Sigma.mk.inj_iff.mp hi).2

@[simp] theorem word_pathFamilyCast (F : Component V → Type z) {a b : V}
    {p q : Quiver.Path a b} (h : p = q)
    (f : ∀ i : Slot p, F (componentAt p i)) :
    word F q (pathFamilyCast F h f) = word F p f := by cases h; rfl

theorem word_joinFamily (F : Component V → Type z) {a b : V} (p : Quiver.Path a b)
    (q : ∀ i : Slot p, Quiver.Path (componentAt p i).source (componentAt p i).target)
    (f : ∀ i : Slot p, ∀ j : Slot (q i), F (componentAt (q i) j)) :
    word F (expand p q) (joinFamily F p q f) = collect p (fun i => word F (q i) (f i)) := by
  unfold word
  rw [collect_expand_slots]
  congr 1
  funext i
  congr 1
  funext j
  have h := expandFamily_joinFamily F p q f i j
  unfold expandFamily at h
  have hh := sigma_transport F (componentAt_slotExpand_symm p q ⟨i,j⟩)
    (joinFamily F p q f ((slotExpand p q).symm ⟨i,j⟩))
  rw [h] at hh
  exact congrArg (fun x => [x]) hh.symm

theorem collect_map {α : Type z} {β : Type z'} (g : α → β) {a b : V}
    (p : Quiver.Path a b) (f : Slot p → List α) :
    (collect p f).map g = collect p (fun i => (f i).map g) := by
  induction p with
  | nil => rfl
  | cons p e ih => simp only [collect, List.map_append, ih]

end WitnessedDecompositions.Dynamic
