import WitnessedDecompositions.Core
import JointArrayLifting

/-! Actual original typed-tree API bridge. Generator names, interfaces, ordered
occurrences and empty children stay in t; coefficient arrays do not replace t. -/
set_option backward.isDefEq.respectTransparency false
namespace WitnessedDecompositions.Tree
universe u v w z
variable {V : Type u} [Quiver.{v} V] {S : Signature.{u,v,w} V}

def InputEdge : {c : Component V} → Tree S c → Type
  | _, .leaf _ => Empty
  | _, .node g children => (i : _) × Option (InputEdge (children i))

def inputEdgeComponent : {c : Component V} → (t : Tree S c) → InputEdge t → Component V
  | _, .leaf _, e => nomatch e
  | _, .node g _children, ⟨i, none⟩ => S.argument g i
  | _, .node g children, ⟨i, some e⟩ => inputEdgeComponent (children i) e

def leafPath : {c : Component V} → (t : Tree S c) → Leaf t → List (InputEdge t)
  | _, .leaf _, _ => []
  | _, .node g children, ⟨i,l⟩ => ⟨i,none⟩ ::
      (leafPath (children i) l).map (fun e => ⟨i,some e⟩)

/-- The old geometry is nonerasing on active components. Empty positions are
retained but impose no fictitious coefficient-bearing descendants. -/
def ActiveSignature (active : Component V → Prop) : Prop :=
  ∀ g, active (S.result g) ↔ ∃ i, active (S.argument g i)

theorem active_root_iff_leaf (active : Component V → Prop)
    (hs : ActiveSignature (S := S) active) {c : Component V} (t : Tree S c) :
    active c ↔ ∃ l : Leaf t, active (leafComponent t l) := by
  induction t with
  | leaf c => simp only [Leaf, leafComponent]; exact ⟨fun h => ⟨(),h⟩,fun h => h.choose_spec⟩
  | node g children ih =>
    rw [hs g]
    constructor
    · rintro ⟨i,hi⟩
      obtain ⟨l,hl⟩ := (ih i).mp hi
      exact ⟨⟨i,l⟩,hl⟩
    · rintro ⟨⟨i,l⟩,hl⟩
      exact ⟨i,(ih i).mpr ⟨l,hl⟩⟩

/-- A shared operation-input edge has one ID even when several final leaves
pass through it. Every active ID occurs on an active final path. -/
theorem active_edge_covered (active : Component V → Prop)
    (hs : ActiveSignature (S := S) active) {c : Component V} (t : Tree S c)
    (e : InputEdge t) (he : active (inputEdgeComponent t e)) :
    ∃ l : Leaf t, active (leafComponent t l) ∧ e ∈ leafPath t l := by
  induction t with
  | leaf c => exact nomatch e
  | node g children ih =>
    rcases e with ⟨i, e⟩
    cases e with
    | none =>
      obtain ⟨l,hl⟩ := (active_root_iff_leaf active hs (children i)).mp he
      exact ⟨⟨i,l⟩,hl,by simp [leafPath]⟩
    | some e =>
      obtain ⟨l,hl,hm⟩ := ih i e he
      refine ⟨⟨i,l⟩,hl,?_⟩
      simp only [leafPath,List.mem_cons]
      exact Or.inr (List.mem_map.mpr ⟨e,hm,rfl⟩)

variable {D : Type*} {E : Type*} [Monoid D] [Monoid E]

/-- Literal one-coefficient-per-active-edge arrays are equivalent to total arrays
with inactive edges fixed at one. Full skeleton data is never quotiented. -/
noncomputable def expandActive {c : Component V} (t : Tree S c)
    (active : Component V → Prop)
    (a : {e : InputEdge t // active (inputEdgeComponent t e)} → D) : InputEdge t → D := by
  classical
  exact fun e => if he : active (inputEdgeComponent t e) then a ⟨e,he⟩ else 1

theorem expandActive_active {c : Component V} (t : Tree S c)
    (active : Component V → Prop)
    (a : {e : InputEdge t // active (inputEdgeComponent t e)} → D)
    (e : {e : InputEdge t // active (inputEdgeComponent t e)}) :
    expandActive t active a e.val = a e := by
  simp [expandActive,e.property]

theorem expandActive_restrict {c : Component V} (t : Tree S c)
    (active : Component V → Prop) (a : InputEdge t → D)
    (ha : ∀ e, ¬active (inputEdgeComponent t e) → a e = 1) :
    expandActive t active (fun e => a e.val) = a := by
  classical
  funext e
  by_cases he : active (inputEdgeComponent t e)
  · simp [expandActive,he]
  · simp [expandActive,he,ha e he]

theorem lift_inactive {A : Type*} (h : D →* E) (inj : Function.Injective h)
    {a : A → D} {b : A → E} (lift : ∀ e, h (a e) = b e)
    {e : A} (he : b e = 1) : a e = 1 :=
  inj ((lift e).trans (he.trans h.map_one.symm))

/-- Source coordinates exist only at active final occurrences. An inactive
leaf path may pass through active ancestors; no product equation is imposed
on such a leaf. Extending inactive *source* leaves by 1 would be wrong. -/
def ActiveLeaf {c : Component V} (t : Tree S c) (active : Component V → Prop) :=
  {l : Leaf t // active (leafComponent t l)}

/-- Active final occurrences partition by their unique active root-input slot.
The equivalence preserves the original ordered slot and recursive leaf IDs. -/
def activeLeafNodeEquiv (active : Component V → Prop)
    (hs : ActiveSignature (S := S) active) (g : S.Generator)
    (children : ∀ i, Tree S (S.argument g i)) :
    ActiveLeaf (.node g children) active ≃
      ((i : {i : Path.Slot (S.input g) // active (S.argument g i)}) ×
        ActiveLeaf (children i.val) active) where
  toFun l := ⟨⟨l.val.1, (active_root_iff_leaf active hs (children l.val.1)).mpr
      ⟨l.val.2,l.property⟩⟩, ⟨l.val.2,l.property⟩⟩
  invFun x := ⟨⟨x.1.val,x.2.val⟩,x.2.property⟩
  left_inv l := by cases l; rfl
  right_inv x := by rcases x with ⟨⟨i,hi⟩,⟨l,hl⟩⟩; rfl

theorem active_source_fixed_coefficient_lift (h : D →* E)
    (inj : Function.Injective h) (fc : JointArrayLifting.FactorClosed h)
    (active : Component V → Prop) (hs : ActiveSignature (S := S) active)
    {c : Component V} (t : Tree S c)
    (source : ActiveLeaf t active → D) (target : InputEdge t → E)
    (inactive : ∀ e, ¬active (inputEdgeComponent t e) → target e = 1)
    (valid : ∀ l : ActiveLeaf t active,
      JointArrayLifting.eval target (leafPath t l.val) = h (source l)) :
    ∃! a : InputEdge t → D,
      (∀ e, h (a e) = target e) ∧
      ∀ l : ActiveLeaf t active, JointArrayLifting.eval a (leafPath t l.val) = source l := by
  classical
  have image : ∀ e, ∃ d, h d = target e := by
    intro e
    by_cases he : active (inputEdgeComponent t e)
    · obtain ⟨l,hl,hm⟩ := active_edge_covered active hs t e he
      exact JointArrayLifting.image_factor h fc target (leafPath t l)
        ⟨source ⟨l,hl⟩,(valid ⟨l,hl⟩).symm⟩ e hm
    · exact ⟨1,(h.map_one).trans (inactive e he).symm⟩
  let a : InputEdge t → D := fun e => Classical.choose (image e)
  have ha : ∀ e, h (a e) = target e := fun e => Classical.choose_spec (image e)
  refine ⟨a,⟨ha,?_⟩,?_⟩
  · intro l
    apply inj
    rw [JointArrayLifting.map_eval, JointArrayLifting.eval_congr ha, valid]
  · intro b hb
    funext e
    exact inj ((hb.1 e).trans (ha e).symm)

/-- At an inactive colour the zero tree has no source coefficient at all. -/
theorem inactive_zero_has_no_source (active : Component V → Prop)
    {c : Component V} (hc : ¬active c) :
    IsEmpty (ActiveLeaf (Tree.leaf (S := S) c) active) :=
  ⟨fun l => hc l.property⟩

/-- At an active colour the literal vertex-free identity forces its one source
coefficient to be 1; this is not applied to empty colours. -/
theorem active_zero_source (active : Component V → Prop)
    {c : Component V} (hc : active c)
    (a : InputEdge (Tree.leaf (S := S) c) → D)
    (source : ActiveLeaf (Tree.leaf (S := S) c) active → D) :
    (∀ l, JointArrayLifting.eval a (leafPath (.leaf c) l.val) = source l) ↔
      source ⟨(),hc⟩ = 1 := by
  constructor
  · intro h; exact (h ⟨(),hc⟩).symm
  · intro h l; rcases l with ⟨⟨⟩,hl⟩; exact h.symm

end WitnessedDecompositions.Tree
