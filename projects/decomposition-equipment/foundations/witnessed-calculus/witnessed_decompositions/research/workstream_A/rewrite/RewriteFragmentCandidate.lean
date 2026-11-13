import GraphCoordinates
import TypedNormalizerAlgebra

/-!
# Substantial typed graph-cut instance for A4

Three interfaces, arbitrary simple graphs on the six-vertex ordered ambient set,
all root supports (including empty), arbitrary finite terms, and Z/3 decorations.
Location is retained witness data, not component colour: `componentCode` uses
only the standardized induced graph and the arrow endpoints.

This candidate is outside the public library pending integration. The explicit
seed/A3 syntax comparison and the programme's broader acceptance remain open.
-/
namespace RewriteFragmentCandidate
open GraphCoordinates TypedNormalizer

abbrev Decoration := ZMod 3
abbrev CutTerm := TypedNormalizer.Term Block Decoration
abbrev CutSpine := TypedNormalizer.Spine Block

/-- All blocks, arrows, intermediate interfaces and decoration are retained.
`whole` is the full standardized adjacency matrix, including cross-block edges.
The root-coordinate partition has an injective standardization on valid blocks,
proved in GraphCoordinates.rankBlock_injective. -/
structure FullCut (a b : Interface) where
  whole : Nat × List Bool
  partition : CutSpine a b
  decoration : Decoration
  deriving DecidableEq

def evaluate {a b : Interface} (g : Graph) (s : Block) (t : CutTerm a b) : FullCut a b :=
  ⟨graphCode g s, t.frontier, t.weight⟩

/-- The root's ordered leaf blocks form an actual vertex partition. -/
def Valid {a b : Interface} (s : Block) (t : CutTerm a b) : Prop :=
  IsPartition s t.frontier.blocks

instance {a b : Interface} (s : Block) (t : CutTerm a b) : Decidable (Valid s t) :=
  inferInstanceAs (Decidable (IsPartition s t.frontier.blocks))

abbrev LocatedTerm (s : Block) (a b : Interface) := {t : CutTerm a b // Valid s t}

theorem evaluate_sound {a b : Interface} (g : Graph) (s : Block)
    {x y : CutTerm a b} (h : E x y) : evaluate g s x = evaluate g s y := by
  have hf := congrArg Prod.fst h.sound
  have hw := congrArg Prod.snd h.sound
  change x.frontier = y.frontier at hf
  change x.weight = y.weight at hw
  simp only [evaluate, hf, hw]

theorem equiv_iff_full_cut_eq {a b : Interface} (g : Graph) (s : Block)
    (x y : CutTerm a b) : E x y ↔ evaluate g s x = evaluate g s y := by
  constructor
  · exact evaluate_sound g s
  · intro h
    apply (equiv_iff_normalize_eq x y).mpr
    exact Prod.ext (congrArg FullCut.partition h) (congrArg FullCut.decoration h)

theorem valid_congr {a b : Interface} (s : Block) {x y : CutTerm a b} (h : E x y) :
    Valid s x ↔ Valid s y := by
  unfold Valid
  rw [h.frontier_eq]

/-- Executable right-comb normalizer on all valid finite graph-cut terms. -/
def normalize {a b : Interface} {s : Block} (t : LocatedTerm s a b) : LocatedTerm s a b :=
  ⟨reify t.val.normalize,
    (valid_congr s (term_equiv_reify_normalize t.val)).mp t.property⟩

theorem normalizer_sound {a b : Interface} {s : Block} (t : LocatedTerm s a b) :
    E t.val (normalize t).val := term_equiv_reify_normalize t.val

/-- Preservation is of the FULL witness, not just pieces or decoration. -/
theorem normalizer_full_witness {a b : Interface} (g : Graph) {s : Block}
    (t : LocatedTerm s a b) : evaluate g s (normalize t).val = evaluate g s t.val :=
  (evaluate_sound g s (normalizer_sound t)).symm

theorem normalizer_idempotent {a b : Interface} {s : Block} (t : LocatedTerm s a b) :
    normalize (normalize t) = normalize t := by
  apply Subtype.ext
  change reify (reify t.val.normalize).normalize = reify t.val.normalize
  rw [normalize_reify]

/-- A graph-cut normal form preserves every embedded leaf block and all typed
intermediate arrows; these are equal typed spines, not equal multisets. -/
theorem normalizer_frontier {a b : Interface} {s : Block} (t : LocatedTerm s a b) :
    (normalize t).val.frontier = t.val.frontier :=
  (normalizer_sound t).frontier_eq.symm

/-- Different local placements and tree shapes agree exactly when their full
flat witnesses agree in this fixed retained whole fibre. -/
theorem equal_normal_forms_iff {a b : Interface} (g : Graph) {s : Block}
    (x y : LocatedTerm s a b) :
    normalize x = normalize y ↔ evaluate g s x.val = evaluate g s y.val := by
  constructor
  · intro h
    have hx := normalizer_full_witness g x
    have hy := normalizer_full_witness g y
    rw [← hx, ← hy, h]
  · intro h
    apply Subtype.ext
    change reify x.val.normalize = reify y.val.normalize
    apply congrArg reify
    exact (equiv_iff_normalize_eq x.val y.val).mp
      ((equiv_iff_full_cut_eq g s x.val y.val).mpr h)

/-- The structural congruence supports genuinely occurrence-indexed insertion.
The separate validity hypothesis ensures replacement subcuts stay in the root. -/
theorem occurrence_substitution_sound {a b : Interface} (g : Graph) (s : Block)
    {x y : CutTerm a b} (h : E x y) (σ : Term.Substitution Block Decoration) (offset : Nat) :
    evaluate g s (x.subst σ offset) = evaluate g s (y.subst σ offset) :=
  evaluate_sound g s (h.subst σ offset)

/-- Validity also transfers across an equation after the same occurrence-indexed
forest has been inserted. This is not an inference from a shared composite alone. -/
theorem occurrence_substitution_valid {a b : Interface} (s : Block)
    {x y : CutTerm a b} (h : E x y) (σ : Term.Substitution Block Decoration) (offset : Nat) :
    Valid s (x.subst σ offset) ↔ Valid s (y.subst σ offset) :=
  valid_congr s (h.subst σ offset)

/-! ## Actual graph-cut construction and coordinate comparison -/

theorem valid_leaf {a b : Interface} (h : a ≤ b) (s : Block) :
    Valid s (.leaf h s : CutTerm a b) := partition_singleton s

theorem valid_unit (a : Interface) : Valid ∅ (.unit a : CutTerm a a) := partition_empty

theorem valid_cut {a b c : Interface} {sx sy : Block}
    {x : CutTerm a b} {y : CutTerm b c}
    (hx : Valid sx x) (hy : Valid sy y) (hd : Disjoint sx sy) :
    Valid (sx ∪ sy) (.cut x y) := by
  change IsPartition (sx ∪ sy) (x.frontier.append y.frontier).blocks
  rw [Spine.blocks_append]
  exact partition_append hx hy hd

/-- Every valid binary node really is a cut: its two retained subgraphs have
exactly disjoint supports whose union is the parent's support. -/
theorem valid_cut_parts {a b c : Interface} {s : Block}
    {x : CutTerm a b} {y : CutTerm b c} (h : Valid s (.cut x y)) :
    Valid (support x.frontier.blocks) x ∧ Valid (support y.frontier.blocks) y ∧
    Disjoint (support x.frontier.blocks) (support y.frontier.blocks) ∧
    support x.frontier.blocks ∪ support y.frontier.blocks = s := by
  change IsPartition s (x.frontier.append y.frontier).blocks at h
  rw [Spine.blocks_append] at h
  exact partition_append_parts h

/-- A replacement is checked against its own occurrence support, independently
of all other occurrences, including repeated component colours and empty blocks. -/
def ValidSubstitution {a b : Interface} (t : CutTerm a b)
    (σ : Term.Substitution Block Decoration) (offset : Nat := 0) : Prop :=
  match t with
  | .leaf h block => Valid block (σ offset h block)
  | .unit _ => True
  | .cut x y => ValidSubstitution x σ offset ∧
      ValidSubstitution y σ (offset + x.leafCount)
  | .deco _ x => ValidSubstitution x σ offset

theorem valid_substitution {a b : Interface} {s : Block} (t : CutTerm a b)
    (ht : Valid s t) (σ : Term.Substitution Block Decoration) (offset : Nat)
    (hσ : ValidSubstitution t σ offset) : Valid s (t.subst σ offset) := by
  induction t generalizing s offset with
  | leaf h block =>
      have hs : block = s := by simpa [Valid, IsPartition, Term.frontier, Spine.blocks] using ht.2
      change Valid block (σ offset h block) at hσ
      simpa only [Term.subst, hs] using hσ
  | unit a => exact ht
  | cut x y ihx ihy =>
      obtain ⟨hx, hy, hd, hs⟩ := valid_cut_parts ht
      obtain ⟨hσx, hσy⟩ := hσ
      simpa only [Term.subst, hs] using
        valid_cut (ihx hx offset hσx) (ihy hy (offset + x.leafCount) hσy) hd
  | deco m x ih => exact ih ht offset hσ

/-- The complete flat witness in the canonical ordered coordinates of its whole. -/
structure StandardCut (s : Block) (a b : Interface) where
  whole : Nat × List Bool
  partition : Spine (Finset (Fin s.card)) a b
  decoration : Decoration
  deriving DecidableEq

def standardEvaluate {a b : Interface} (g : Graph) (s : Block) (t : CutTerm a b) :
    StandardCut s a b :=
  ⟨graphCode g s, t.frontier.map (rankBlock s), t.weight⟩

/-- Root-coordinate locations are only a coordinate representation: equality of
standardized full cuts reflects the SAME mixed congruence on valid terms. -/
theorem equiv_iff_standard_cut_eq {a b : Interface} (g : Graph) (s : Block)
    (x y : CutTerm a b) (hx : Valid s x) (hy : Valid s y) :
    E x y ↔ standardEvaluate g s x = standardEvaluate g s y := by
  constructor
  · intro h
    have hf := h.frontier_eq
    have hw := congrArg Prod.snd h.sound
    change x.weight = y.weight at hw
    simp only [standardEvaluate, hf, hw]
  · intro h
    have hf := congrArg StandardCut.partition h
    have hw := congrArg StandardCut.decoration h
    change x.frontier.map (rankBlock s) = y.frontier.map (rankBlock s) at hf
    have hfront : x.frontier = y.frontier := by
      apply Spine.map_eq_of_injOn (rankBlock s) x.frontier y.frontier _ hf
      intro p hp q hq heq
      have hps : p ⊆ s := partition_block_subset hx hp
      have hqs : q ⊆ s := partition_block_subset hy hq
      exact congrArg Subtype.val (rankBlock_injective s (a₁ := ⟨p,hps⟩) (a₂ := ⟨q,hqs⟩) heq)
    apply (equiv_iff_normalize_eq x y).mpr
    exact Prod.ext hfront hw

/-- Every finite independent tuple extends to the total occurrence dispatch API.
No equality test on leaf payloads is needed, and outside-frontier values default
to identity leaves. This construction is used at the actual spine positions. -/
def extendFiniteTuple {n : Nat} (src dst : Fin n → Interface)
    (forest : ∀ i, CutTerm (src i) (dst i)) : Term.Substitution Block Decoration :=
  fun position {a b} h block =>
    if hi : position < n then
      if ha : src ⟨position, hi⟩ = a then
        if hb : dst ⟨position, hi⟩ = b then
          ha ▸ hb ▸ forest ⟨position, hi⟩
        else .leaf h block
      else .leaf h block
    else .leaf h block

theorem extendFiniteTuple_at {n : Nat} (src dst : Fin n → Interface)
    (forest : ∀ i, CutTerm (src i) (dst i)) (i : Fin n)
    (h : src i ≤ dst i) (block : Block) :
    extendFiniteTuple src dst forest i.val h block = forest i := by
  simp [extendFiniteTuple, i.isLt]

/-- Actual ordered occurrence positions of the authoritative typed frontier. -/
abbrev FrontierIndex {a b : Interface} (t : CutTerm a b) := Fin t.frontier.entries.length

def frontierEntry {a b : Interface} (t : CutTerm a b) (i : FrontierIndex t) :
    Spine.Entry Block := t.frontier.entries.get i

abbrev FrontierForest {a b : Interface} (t : CutTerm a b) :=
  ∀ i : FrontierIndex t, CutTerm (frontierEntry t i).source (frontierEntry t i).target

def frontierDispatch {a b : Interface} (t : CutTerm a b) (forest : FrontierForest t) :
    Term.Substitution Block Decoration :=
  extendFiniteTuple (fun i => (frontierEntry t i).source)
    (fun i => (frontierEntry t i).target) forest

/-- Every independently chosen finite frontier forest is available to subst. -/
theorem frontierDispatch_at {a b : Interface} (t : CutTerm a b) (forest : FrontierForest t)
    (i : FrontierIndex t) :
    frontierDispatch t forest i.val (frontierEntry t i).arrow (frontierEntry t i).block =
      forest i :=
  extendFiniteTuple_at _ _ forest i (frontierEntry t i).arrow (frontierEntry t i).block

/-- Graph validity is checked at EACH original occurrence, not by demanding that
all equal colours receive a common replacement. -/
theorem frontierDispatch_valid_at {a b : Interface} (t : CutTerm a b)
    (forest : FrontierForest t)
    (hforest : ∀ i, Valid (frontierEntry t i).block (forest i)) (i : FrontierIndex t) :
    Valid (frontierEntry t i).block
      (frontierDispatch t forest i.val (frontierEntry t i).arrow (frontierEntry t i).block) := by
  rw [frontierDispatch_at]
  exact hforest i

theorem validSubstitution_iff_allLeaves {a b : Interface} (t : CutTerm a b)
    (σ : Term.Substitution Block Decoration) (offset : Nat) :
    ValidSubstitution t σ offset ↔
      t.AllLeaves (fun position e => Valid e.block (σ position e.arrow e.block)) offset := by
  induction t generalizing offset with
  | leaf h block => rfl
  | unit a => rfl
  | cut x y ihx ihy =>
      exact and_congr (ihx offset) (ihy (offset + x.leafCount))
  | deco m x ih => exact ih offset

/-- The recursive offsets used by substitution are exactly the ordered entries'
positions. Therefore every valid finite independent frontier forest is valid
for the actual recursive substitution, not just for isolated dispatch calls. -/
theorem frontierDispatch_valid {a b : Interface} (t : CutTerm a b)
    (forest : FrontierForest t)
    (hforest : ∀ i, Valid (frontierEntry t i).block (forest i)) :
    ValidSubstitution t (frontierDispatch t forest) 0 := by
  rw [validSubstitution_iff_allLeaves]
  apply (Term.allLeaves_iff_entries _ _ _).mpr
  intro i
  simpa only [Nat.zero_add, frontierEntry] using frontierDispatch_valid_at t forest hforest i

/-- End-to-end valid graph-cut grafting for EVERY independent finite forest. -/
theorem valid_frontierForest_graft {a b : Interface} {s : Block} (t : CutTerm a b)
    (ht : Valid s t) (forest : FrontierForest t)
    (hforest : ∀ i, Valid (frontierEntry t i).block (forest i)) :
    Valid s (t.subst (frontierDispatch t forest) 0) :=
  valid_substitution t ht _ 0 (frontierDispatch_valid t forest hforest)

theorem normalizer_irreducible {a b : Interface} {s : Block} (t : LocatedTerm s a b)
    (q : CutTerm a b) : ¬ Step (normalize t).val q :=
  reify_irreducible t.val.normalize q

/-! ## Concrete mixed examples -/

def l0 : CutTerm 0 1 := .leaf (by decide) b0
def l1 : CutTerm 1 1 := .leaf (by decide) b1
def l2 : CutTerm 1 1 := .leaf (by decide) b2
def l3 : CutTerm 1 2 := .leaf (by decide) b3

def leftMixed : CutTerm 0 2 :=
  .cut (.cut (.cut l0 (.deco 1 l1)) (.deco 2 l2)) l3

def rightBare : CutTerm 0 2 := .cut l0 (.cut l1 (.cut l2 l3))

theorem leftMixed_valid : Valid Finset.univ leftMixed := by
  exact six_partition

theorem rightBare_valid : Valid Finset.univ rightBare := by
  exact six_partition

/-- Rotation, both decoration movements, and nontrivial aggregation interact. -/
theorem mixed_example : E leftMixed rightBare := by
  apply (equiv_iff_normalize_eq _ _).mpr
  apply Prod.ext
  · rfl
  · change (0 + (1 + 0) + (2 + 0) + 0 : Decoration) = 0 + (0 + (0 + 0))
    decide

theorem mixed_example_full_cut :
    evaluate sixGraph Finset.univ leftMixed = evaluate sixGraph Finset.univ rightBare :=
  evaluate_sound _ _ mixed_example

/-- The six-vertex mixed profile has two repeated nonempty component colours. -/
theorem genuine_repeated_components :
    b1.Nonempty ∧ b2.Nonempty ∧ b1 ≠ b2 ∧
    componentCode sixGraph b1 1 1 = componentCode sixGraph b2 1 1 :=
  ⟨repeated_nonempty.1, repeated_nonempty.2.1, repeated_nonempty.2.2,
    repeated_component⟩

def decoratedUnit : CutTerm 0 1 := .cut (.deco 1 (.unit 0)) l0

theorem decorated_unit_not_lost : E decoratedUnit (.deco 1 l0) :=
  E.trans (E.DL 1 (.unit 0) l0) (E.deco 1 (E.UL l0))

def emptyLeaf : CutTerm 1 1 := .leaf (by decide) ∅

theorem empty_leaf_not_nullary : ¬ E emptyLeaf (.unit 1 : CutTerm 1 1) := by
  intro h
  have hf := h.frontier_eq
  cases hf

/-- Multiple empty-support identity leaves remain independent occurrences. -/
def twoEmpty : CutTerm 1 1 := .cut emptyLeaf emptyLeaf

def distinguishOccurrences : Term.Substitution Block Decoration :=
  fun position {_a _b} h block => if position = 0 then .deco 1 (.leaf h block) else .leaf h block

theorem first_empty_occurrence_only :
    twoEmpty.subst distinguishOccurrences = .cut (.deco 1 emptyLeaf) emptyLeaf := by
  rfl

/-- Empty graph does not force an identity interface arrow. -/
def nonidentityEmpty : CutTerm 0 1 := .leaf (by decide) ∅

theorem nonidentity_empty_frontier : nonidentityEmpty.frontier.length = 1 := rfl

theorem same_pieces_different_wholes :
    (evaluate sixGraph Finset.univ rightBare).whole ≠
      (evaluate missingCrossEdge Finset.univ rightBare).whole :=
  different_retained_wholes

/-- Distinct refinements at the two repeated NONEMPTY components. -/
def splitFirstMiddle : CutTerm 1 1 :=
  .cut (b := 1) (.leaf (by decide) {1}) (.leaf (by decide) {2})
def splitSecondMiddle : CutTerm 1 1 :=
  .cut (b := 1) (.leaf (by decide) {3}) (.leaf (by decide) {4})
def refinedFirst : CutTerm 0 2 := .cut l0 (.cut splitFirstMiddle (.cut l2 l3))
def refinedSecond : CutTerm 0 2 := .cut l0 (.cut l1 (.cut splitSecondMiddle l3))

theorem refinedFirst_valid : Valid Finset.univ refinedFirst := by decide
theorem refinedSecond_valid : Valid Finset.univ refinedSecond := by decide

theorem different_repeated_occurrence_refinements : ¬ E refinedFirst refinedSecond := by
  intro h
  have hn : refinedFirst.normalize ≠ refinedSecond.normalize := by decide
  exact hn h.sound

/-- Equal input colours do not identify distinct retained vertex partitions. -/
def partition01 : CutTerm 0 2 :=
  .cut (b := 1) (.leaf (by decide) {0}) (.leaf (by decide) {1})
def partition10 : CutTerm 0 2 :=
  .cut (b := 1) (.leaf (by decide) {1}) (.leaf (by decide) {0})

def frontierColours {a b : Interface} (g : Graph) (t : CutTerm a b) :=
  t.frontier.entries.map fun e => componentCode g e.block e.source e.target

theorem identical_profile_different_partition :
    Valid {0,1} partition01 ∧ Valid {0,1} partition10 ∧
    frontierColours sixGraph partition01 = frontierColours sixGraph partition10 ∧
    ¬ E partition01 partition10 := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro h
  have hn : partition01.normalize ≠ partition10.normalize := by decide
  exact hn h.sound

/- An ill-typed cut cannot be formed. The first term ends at 1 while the second
begins at 0. This guarded negative check must continue to fail elaboration. -/
example : True := by
  fail_if_success have bad := Term.cut l0 l0
  trivial

#print axioms normalizer_sound
#print axioms normalizer_full_witness
#print axioms equal_normal_forms_iff
#print axioms equiv_iff_standard_cut_eq
#print axioms normalizer_irreducible
#print axioms valid_substitution
#print axioms frontierDispatch_at
#print axioms frontierDispatch_valid
#print axioms valid_frontierForest_graft
#print axioms repeated_component
#print axioms different_repeated_occurrence_refinements

end RewriteFragmentCandidate
