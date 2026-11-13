import Mathlib.Data.Finset.Sort
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! Coordinate model for the A4 worked graph-cut instance. Locations are witness
inclusions, never component colours. All computations retain an actual simple
ordered graph, not only a list of untyped leaf names. -/
namespace GraphCoordinates

abbrev Vertex := Fin 6
abbrev Block := Finset Vertex

structure Graph where
  edge : Vertex → Vertex → Bool
  symmetric : ∀ i j, edge i j = edge j i
  loopless : ∀ i, edge i i = false

/-- The increasing enumeration is the declared canonical relabeling convention. -/
def inclusion (s : Block) : Fin s.card ↪o Vertex :=
  s.orderEmbOfFin rfl

/-- Standardized graph adjacency, with its vertex count carried by the type. -/
def inducedEdge (g : Graph) (s : Block) (i j : Fin s.card) : Bool :=
  g.edge (inclusion s i) (inclusion s j)

theorem induced_symmetric (g : Graph) (s : Block) (i j : Fin s.card) :
    inducedEdge g s i j = inducedEdge g s j i :=
  g.symmetric _ _

theorem induced_loopless (g : Graph) (s : Block) (i : Fin s.card) :
    inducedEdge g s i i = false :=
  g.loopless _

/-- Kernel-computable increasing enumeration of an ambient support. -/
def enumerate (s : Block) : List Vertex :=
  (List.finRange 6).filter fun v => v ∈ s

theorem enumerate_eq_sort (s : Block) : enumerate s = s.sort := by
  have hs : (enumerate s).SortedLT :=
    (List.Pairwise.filter _ (List.sortedLT_finRange 6).pairwise).sortedLT
  exact hs.eq_of_mem_iff (Finset.sortedLT_sort s) (by intro a; simp [enumerate])

/-- A computable canonical code, independent of the ambient locations. -/
def graphCode (g : Graph) (s : Block) : Nat × List Bool :=
  (s.card, (enumerate s).flatMap fun i => (enumerate s).map fun j => g.edge i j)

/-- A component colour does not contain its embedding in the root graph. -/
def componentCode (g : Graph) (s : Block) (a b : Fin 3) :
    (Nat × List Bool) × (Fin 3 × Fin 3) :=
  (graphCode g s, (a, b))

/-- An included block, expressed in canonical coordinates of its root support. -/
def rankBlock (s b : Block) : Finset (Fin s.card) :=
  Finset.univ.filter fun i => inclusion s i ∈ b

@[simp] theorem mem_rankBlock (s b : Block) (i : Fin s.card) :
    i ∈ rankBlock s b ↔ inclusion s i ∈ b := by
  simp [rankBlock]

theorem inclusion_mem (s : Block) (i : Fin s.card) : inclusion s i ∈ s :=
  Finset.orderEmbOfFin_mem s rfl i

/-- Pulling a standardized block back into the ambient root recovers it exactly.
The subset hypothesis is essential: out-of-root vertices are not observable. -/
theorem recover_rankBlock (s b : Block) (hb : b ⊆ s) :
    (rankBlock s b).image (inclusion s) = b := by
  ext v
  constructor
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨i, hi, rfl⟩
    exact (mem_rankBlock s b i).mp hi
  · intro hv
    let x : s := ⟨v, hb hv⟩
    let i : Fin s.card := (s.orderIsoOfFin rfl).symm x
    have hi : inclusion s i = v := by
      change ((s.orderIsoOfFin rfl) ((s.orderIsoOfFin rfl).symm x)).val = v
      simp [x]
    apply Finset.mem_image.mpr
    refine ⟨i, ?_, hi⟩
    apply (mem_rankBlock s b i).mpr
    simpa only [hi] using hv

 theorem rankBlock_injective (s : Block) :
    Function.Injective (fun b : {b : Block // b ⊆ s} => rankBlock s b.val) := by
  intro b c h
  apply Subtype.ext
  have := congrArg (fun q : Finset (Fin s.card) => q.image (inclusion s)) h
  simpa only [recover_rankBlock s b.val b.property,
    recover_rankBlock s c.val c.property] using this

/-- An ordered partition retains its full ordered block list, including empty
blocks. Nonoverlap and coverage are separate, checkable properties. -/
def IsPartition (s : Block) (blocks : List Block) : Prop :=
  blocks.Pairwise Disjoint ∧ blocks.foldr (· ∪ ·) ∅ = s

instance (s : Block) (bs : List Block) : Decidable (IsPartition s bs) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem partition_empty : IsPartition ∅ [] := by
  simp [IsPartition]

theorem partition_singleton (s : Block) : IsPartition s [s] := by
  simp [IsPartition]

/-- Union support of an ordered list of blocks. -/
def support (bs : List Block) : Block := bs.foldr (· ∪ ·) ∅

theorem support_append (xs ys : List Block) :
    support (xs ++ ys) = support xs ∪ support ys := by
  induction xs with
  | nil => simp [support]
  | cons x xs ih => simpa [support, Finset.union_assoc] using congrArg (x ∪ ·) ih

theorem block_subset_support {bs : List Block} {b : Block} (h : b ∈ bs) :
    b ⊆ support bs := by
  induction bs with
  | nil => simp at h
  | cons x xs ih =>
      rcases List.mem_cons.mp h with rfl | h
      · exact Finset.subset_union_left
      · exact Finset.Subset.trans (ih h) Finset.subset_union_right

theorem partition_block_subset {s : Block} {bs : List Block} (h : IsPartition s bs)
    {b : Block} (hb : b ∈ bs) : b ⊆ s := by
  have hs : support bs = s := h.2
  rw [← hs]
  exact block_subset_support hb

@[simp] theorem mem_support (v : Vertex) (bs : List Block) :
    v ∈ support bs ↔ ∃ b ∈ bs, v ∈ b := by
  induction bs with
  | nil => simp [support]
  | cons b bs ih =>
      simp only [support] at ih
      simp [support, ih]

theorem partition_append_parts {s : Block} {xs ys : List Block}
    (h : IsPartition s (xs ++ ys)) :
    IsPartition (support xs) xs ∧ IsPartition (support ys) ys ∧
    Disjoint (support xs) (support ys) ∧ support xs ∪ support ys = s := by
  have hp := List.pairwise_append.mp h.1
  refine ⟨⟨hp.1, rfl⟩, ⟨hp.2.1, rfl⟩, ?_, ?_⟩
  · apply Finset.disjoint_left.mpr
    intro v hvx hvy
    rcases (mem_support v xs).mp hvx with ⟨x, hx, hvx⟩
    rcases (mem_support v ys).mp hvy with ⟨y, hy, hvy⟩
    exact Finset.disjoint_left.mp (hp.2.2 x hx y hy) hvx hvy
  · rw [← support_append]
    exact h.2

theorem partition_append {sx sy : Block} {xs ys : List Block}
    (hx : IsPartition sx xs) (hy : IsPartition sy ys) (hd : Disjoint sx sy) :
    IsPartition (sx ∪ sy) (xs ++ ys) := by
  constructor
  · rw [List.pairwise_append]
    refine ⟨hx.1, hy.1, ?_⟩
    intro x hx' y hy'
    exact hd.mono (partition_block_subset hx hx') (partition_block_subset hy hy')
  · change support (xs ++ ys) = sx ∪ sy
    rw [support_append]
    exact congrArg₂ (· ∪ ·) hx.2 hy.2

/-- Example whole with internal and cross-block edges. -/
def sixGraph : Graph where
  edge i j := decide ((i.val, j.val) ∈
    [(1,2), (2,1), (3,4), (4,3), (0,5), (5,0), (2,3), (3,2)])
  symmetric := by decide
  loopless := by decide

def b0 : Block := {0}
def b1 : Block := {1, 2}
def b2 : Block := {3, 4}
def b3 : Block := {5}

theorem six_partition : IsPartition Finset.univ [b0, b1, b2, b3] := by decide

theorem repeated_nonempty : b1.Nonempty ∧ b2.Nonempty ∧ b1 ≠ b2 := by decide

/-- The two different located blocks really are the SAME component type. -/
theorem repeated_component :
    componentCode sixGraph b1 1 1 = componentCode sixGraph b2 1 1 := by decide

/-- An altered whole with the same input graphs. -/
def missingCrossEdge : Graph where
  edge i j := decide ((i.val, j.val) ∈
    [(1,2), (2,1), (3,4), (4,3), (2,3), (3,2)])
  symmetric := by decide
  loopless := by decide

theorem same_restricted_pieces :
    [b0,b1,b2,b3].map (graphCode sixGraph) =
      [b0,b1,b2,b3].map (graphCode missingCrossEdge) := by decide

theorem different_retained_wholes :
    graphCode sixGraph Finset.univ ≠ graphCode missingCrossEdge Finset.univ := by decide

/-- A nonidentity empty component is different from every designated unit at
its source, despite having the same empty graph. -/
theorem empty_nonidentity_not_source_unit :
    componentCode sixGraph ∅ 0 1 ≠ componentCode sixGraph ∅ 0 0 := by decide

end GraphCoordinates
