import TreeArrayBridge
import GraphCutFragment

/-! Concrete bridge to the recovered graph-coloured Signature and original Tree
API. This is the existing size-at-most-six graph representative, with arbitrary
finite trees, full typed graph colours and ordered empty positions. -/
set_option backward.isDefEq.respectTransparency false
namespace WitnessedDecompositions.GraphCut
open GraphCoordinates

def active (c : Component Interface) : Prop := 0 < c.edge.graph.val.1

theorem binary_active (g : BinaryCut) :
    0 < g.whole.val.1 ↔ 0 < g.left.val.1 ∨ 0 < g.right.val.1 := by
  obtain ⟨G,s,u,v,hp,hw,hl,hr,_,_⟩ := g.valid
  rw [hw,hl,hr]
  change 0 < s.card ↔ 0 < u.card ∨ 0 < v.card
  have hu : u ∪ v = s := by simpa using hp.2
  rw [←hu]
  simp only [Finset.card_pos, Finset.union_nonempty]

theorem cutSignature_active : Tree.ActiveSignature (S := cutSignature) active := by
  intro g
  cases g with
  | inl g =>
    change 0 < g.whole.val.1 ↔ ∃ i : Path.Slot (cutSignature.input (.inl g)),
      active (cutSignature.argument (.inl g) i)
    rw [binary_active]
    constructor
    · intro h
      cases h with
      | inl h => exact ⟨.inl (.inr ()), h⟩
      | inr h => exact ⟨.inr (), h⟩
    · rintro ⟨i,hi⟩
      cases i with
      | inl i => cases i with
        | inl i => exact nomatch i
        | inr i => exact Or.inl hi
      | inr i => exact Or.inr hi
  | inr a =>
    constructor
    · intro h
      change 0 < (∅ : Block).card at h
      simp at h
    · rintro ⟨i,_⟩
      exact nomatch i

/-- Arbitrary finite original graph trees inherit the coefficient-array lift.
No graph witnesses, graph adjacencies, interfaces or occurrence slots are erased. -/
theorem graph_source_fixed_lift {D E : Type*} [Monoid D] [Monoid E]
    (h : D →* E) (inj : Function.Injective h)
    (fc : JointArrayLifting.FactorClosed h) {c : Component Interface}
    (t : CutTree c) (source : Tree.ActiveLeaf t active → D) (target : t.InputEdge → E)
    (inactive : ∀ e, ¬active (t.inputEdgeComponent e) → target e = 1)
    (valid : ∀ l, JointArrayLifting.eval target (t.leafPath l.val) = h (source l)) :
    ∃! a : t.InputEdge → D,
      (∀ e, h (a e) = target e) ∧
      ∀ l, JointArrayLifting.eval a (t.leafPath l.val) = source l :=
  Tree.active_source_fixed_coefficient_lift h inj fc active cutSignature_active t
    source target inactive valid

/-- A retained empty occurrence can sit below a nonempty parent edge.
Its path product need not be 1: it is not a source coordinate. -/
def emptySplit : BinaryCut :=
  binaryCut sixGraph {0} {0} ∅ (by simp [IsPartition]) 0 0 0 le_rfl le_rfl

def activeLeafTree : CutTree (component sixGraph {0} 0 0 le_rfl) := .leaf _
def emptyLeafTree : CutTree (component sixGraph ∅ 0 0 le_rfl) := .leaf _
def nestedEmpty : CutTree (component sixGraph {0} 0 0 le_rfl) :=
  cut (g := emptySplit) (cut (g := emptySplit) activeLeafTree emptyLeafTree) emptyLeafTree

def retainedEmpty : nestedEmpty.Leaf := ⟨.inl (.inr ()), ⟨.inr (), ()⟩⟩

def emptyExampleLabels : nestedEmpty.InputEdge → Nat
  | ⟨.inl (.inl i), _⟩ => nomatch i
  | ⟨.inl (.inr ()), none⟩ => 2
  | _ => 1

theorem retained_empty_inactive : ¬active (nestedEmpty.leafComponent retainedEmpty) := by
  change ¬ 0 < (∅ : Block).card
  simp

theorem retained_empty_path_not_unit :
    JointArrayLifting.eval emptyExampleLabels (nestedEmpty.leafPath retainedEmpty) = 2 := by
  decide

end WitnessedDecompositions.GraphCut
