import RankSensitiveCompression
import JointQuotientDecoder

/-! Rank-sensitive compression on the original typed tree with inactive slots
retained in its skeleton and omitted only from coefficient profiles. -/
set_option backward.isDefEq.respectTransparency false
namespace RankSensitiveCompression
universe u v
variable {G : Type u} {K : Type v} [Group G] [Group K]

theorem obs_comp_equiv (h : G →* K) {I J : Type*} (e : I ≃ J)
    {a b : J → G} (hab : ObsEq h a b) :
    ObsEq h (fun i => a (e i)) (fun i => b (e i)) := by
  constructor
  · intro hi
    have hj : Subsingleton J := ⟨fun j k => by
      have he := hi.elim (e.symm j) (e.symm k)
      exact (e.symm.injective he)⟩
    rw [hab.1 hj]
  · intro i; exact hab.2 (e i)

open WitnessedDecompositions
variable {V : Type*} [Quiver V] {S : Signature V}

def ActiveDecoration (G : Type u) (active : Component V → Prop) :
    {c : Component V} → Tree S c → Type u
  | _, .leaf _ => PUnit.{u+1}
  | _, .node g children =>
      ({i : Path.Slot (S.input g) // active (S.argument g i)} → G) ×
      ((i : Path.Slot (S.input g)) → ActiveDecoration G active (children i))

def activeEvaluate (active : Component V → Prop) (hs : Tree.ActiveSignature (S := S) active) :
    {c : Component V} → (t : Tree S c) →
    ActiveDecoration G active t → Tree.ActiveLeaf t active → G
  | _, .leaf _, _ => fun _ => 1
  | _, .node g children, d => fun l =>
      graft d.1 (fun i => activeEvaluate active hs (children i.val) (d.2 i.val))
        (Tree.activeLeafNodeEquiv active hs g children l)

def ActiveDecorationEq (h : G →* K) (active : Component V → Prop) :
    {c : Component V} → (t : Tree S c) →
    ActiveDecoration G active t → ActiveDecoration G active t → Prop
  | _, .leaf _, _, _ => True
  | _, .node _ children, d, e => ObsEq h d.1 e.1 ∧
      ∀ i, ActiveDecorationEq h active (children i) (d.2 i) (e.2 i)

lemma active_child_nonempty (active : Component V → Prop)
    (hs : Tree.ActiveSignature (S := S) active) (g : S.Generator)
    (children : ∀ i, Tree S (S.argument g i))
    (i : {i : Path.Slot (S.input g) // active (S.argument g i)}) :
    Nonempty (Tree.ActiveLeaf (children i.val) active) := by
  obtain ⟨l, hl⟩ := (Tree.active_root_iff_leaf active hs (children i.val)).mp i.property
  exact ⟨⟨l,hl⟩⟩

theorem active_evaluate_congr (h : G →* K) (active : Component V → Prop)
    (hs : Tree.ActiveSignature (S := S) active) {c : Component V} (t : Tree S c)
    {d e : ActiveDecoration G active t} (hd : ActiveDecorationEq h active t d e) :
    ObsEq h (activeEvaluate active hs t d) (activeEvaluate active hs t e) := by
  induction t with
  | leaf c => exact obs_refl h _
  | node g children ih =>
    exact obs_comp_equiv h (Tree.activeLeafNodeEquiv active hs g children)
      (graft_congr h (active_child_nonempty active hs g children) hd.1
        (fun i => ih i.val (hd.2 i.val)))

/-- All original typed trees, including arbitrarily many inactive positions,
nullary vertices and vertex-free identities. Rank means active rank only. -/
theorem active_all_tree_lift (h : G →* K) (active : Component V → Prop)
    (hs : Tree.ActiveSignature (S := S) active) {c : Component V} (t : Tree S c)
    (x : Tree.ActiveLeaf t active → G) (d : ActiveDecoration G active t)
    (valid : ObsEq h x (activeEvaluate active hs t d)) :
    ∃ e : ActiveDecoration G active t,
      ActiveDecorationEq h active t e d ∧ activeEvaluate active hs t e = x := by
  induction t with
  | leaf c =>
    refine ⟨PUnit.unit, trivial, ?_⟩
    have sub : Subsingleton (Tree.ActiveLeaf (Tree.leaf (S := S) c) active) :=
      ⟨fun a b => Subtype.ext (show a.val = b.val from (show Subsingleton Unit from inferInstance).elim _ _)⟩
    exact (valid.1 sub).symm
  | node g children ih =>
    classical
    let eqv := Tree.activeLeafNodeEquiv active hs g children
    let x' := fun s => x (eqv.symm s)
    have valid' : ObsEq h x' (graft d.1
        (fun i => activeEvaluate active hs (children i.val) (d.2 i.val))) := by
      have hh := obs_comp_equiv h eqv.symm valid
      simpa only [activeEvaluate, eqv, x', Equiv.apply_symm_apply] using hh
    obtain ⟨a,b,ha,hb,hx⟩ := root_lift h
      (active_child_nonempty active hs g children) x' d.1
      (fun i => activeEvaluate active hs (children i.val) (d.2 i.val)) valid'
    let childSource : (i : Path.Slot (S.input g)) → Tree.ActiveLeaf (children i) active → G :=
      fun i => if hi : active (S.argument g i) then b ⟨i,hi⟩
        else activeEvaluate active hs (children i) (d.2 i)
    have childValid : ∀ i, ObsEq h (childSource i)
        (activeEvaluate active hs (children i) (d.2 i)) := by
      intro i
      dsimp only [childSource]
      split_ifs with hi
      · exact hb ⟨i,hi⟩
      · exact obs_refl h _
    have lifts : ∀ i, ∃ e : ActiveDecoration G active (children i),
        ActiveDecorationEq h active (children i) e (d.2 i) ∧
        activeEvaluate active hs (children i) e = childSource i :=
      fun i => ih i (childSource i) (d.2 i) (childValid i)
    choose es hes evals using lifts
    refine ⟨(a,es),⟨ha,hes⟩,?_⟩
    funext l
    change graft a (fun i => activeEvaluate active hs (children i.val) (es i.val))
      (eqv l) = x l
    have echild : (fun i : {i : Path.Slot (S.input g) // active (S.argument g i)} => activeEvaluate active hs (children i.val) (es i.val)) = b := by
      funext i
      rw [evals i.val]
      simp only [childSource, dite_eq_left i.property]
    rw [echild, hx]
    exact congrArg x (eqv.symm_apply_apply l)

theorem active_exact_tree_decoder (h : G →* K) (active : Component V → Prop)
    (hs : Tree.ActiveSignature (S := S) active) {c : Component V} (t : Tree S c)
    (x : Tree.ActiveLeaf t active → G) (d : ActiveDecoration G active t) :
    ObsEq h x (activeEvaluate active hs t d) ↔
      ∃ e : ActiveDecoration G active t,
        ActiveDecorationEq h active t e d ∧ activeEvaluate active hs t e = x := by
  constructor
  · exact active_all_tree_lift h active hs t x d
  · rintro ⟨e,he,hx⟩
    rw [← hx]
    exact active_evaluate_congr h active hs t he

/-- The actual quotient relation, rather than an assumed decoder. -/
def observationSetoid (h : G →* K) (I : Type*) : Setoid (I → G) where
  r := ObsEq h
  iseqv := ⟨obs_refl h, fun he => obs_symm h he, fun he hf => obs_trans h he hf⟩

theorem active_decoration_refl (h : G →* K) (active : Component V → Prop)
    {c : Component V} (t : Tree S c) (d : ActiveDecoration G active t) :
    ActiveDecorationEq h active t d d := by
  induction t with
  | leaf c => trivial
  | node g children ih => exact ⟨obs_refl h _, fun i => ih i (d.2 i)⟩

theorem active_decoration_symm (h : G →* K) (active : Component V → Prop)
    {c : Component V} (t : Tree S c) {d e : ActiveDecoration G active t}
    (he : ActiveDecorationEq h active t d e) : ActiveDecorationEq h active t e d := by
  induction t with
  | leaf c => trivial
  | node g children ih => exact ⟨obs_symm h he.1, fun i => ih i (he.2 i)⟩

theorem active_decoration_trans (h : G →* K) (active : Component V → Prop)
    {c : Component V} (t : Tree S c) {d e f : ActiveDecoration G active t}
    (he : ActiveDecorationEq h active t d e) (hf : ActiveDecorationEq h active t e f) :
    ActiveDecorationEq h active t d f := by
  induction t with
  | leaf c => trivial
  | node g children ih => exact ⟨obs_trans h he.1 hf.1, fun i => ih i (he.2 i) (hf.2 i)⟩

def activeDecorationSetoid (h : G →* K) (active : Component V → Prop)
    {c : Component V} (t : Tree S c) : Setoid (ActiveDecoration G active t) where
  r := ActiveDecorationEq h active t
  iseqv := ⟨active_decoration_refl h active t,
    fun he => active_decoration_symm h active t he,
    fun he hf => active_decoration_trans h active t he hf⟩

/-- Whole record images transfer to every representative of a source code. -/
theorem active_record_transport (h : G →* K) (active : Component V → Prop)
    (hs : Tree.ActiveSignature (S := S) active) {c : Component V} (t : Tree S c)
    {x y : Tree.ActiveLeaf t active → G} (hxy : ObsEq h x y)
    (b : Quotient (activeDecorationSetoid h active t)) :
    JointQuotientDecoder.RecordImage
      (fun x d => activeEvaluate active hs t d = x)
      (Quotient.mk (activeDecorationSetoid h active t)) x b →
    JointQuotientDecoder.RecordImage
      (fun x d => activeEvaluate active hs t d = x)
      (Quotient.mk (activeDecorationSetoid h active t)) y b := by
  rintro ⟨d, hd, hb⟩
  have valid : ObsEq h y (activeEvaluate active hs t d) := by
    rw [hd]; exact obs_symm h hxy
  obtain ⟨e, he, hy⟩ := active_all_tree_lift h active hs t y d valid
  exact ⟨e,hy,(Quotient.sound he).trans hb⟩

/-- Concrete instantiation of the abstract exact-decoder equation. Its lifting
premise is discharged by the all-depth group construction, not assumed. -/
theorem active_quotient_exact (h : G →* K) (active : Component V → Prop)
    (hs : Tree.ActiveSignature (S := S) active) {c : Component V} (t : Tree S c) :
    JointQuotientDecoder.ExactDecoder
      (fun x d => activeEvaluate active hs t d = x)
      (JointQuotientDecoder.QuotientRelation
        (fun x d => activeEvaluate active hs t d = x)
        (Quotient.mk (observationSetoid h (Tree.ActiveLeaf t active)))
        (Quotient.mk (activeDecorationSetoid h active t)))
      (Quotient.mk (observationSetoid h (Tree.ActiveLeaf t active)))
      (Quotient.mk (activeDecorationSetoid h active t)) := by
  apply (JointQuotientDecoder.quotient_exact_iff_stable _ _ _).mpr
  intro x y hxy b
  have he : ObsEq h x y := Quotient.exact hxy
  exact ⟨active_record_transport h active hs t he b,
    active_record_transport h active hs t (obs_symm h he) b⟩

end RankSensitiveCompression
