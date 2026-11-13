import ActiveRankSensitiveCompression
import GraphCoefficientBridge

/-! Connect the positive rank-sensitive calculus to exactly the same original
Tree input-edge arrays used by source-fixed lifting and graph comparisons. -/
set_option backward.isDefEq.respectTransparency false
namespace RankSensitiveCompression
open WitnessedDecompositions
universe u
variable {G : Type u} [Group G]
variable {V : Type*} [Quiver V] {S : Signature V}

noncomputable def activeEdgeLabels (active : Component V → Prop) :
    {c : Component V} → (t : Tree S c) → ActiveDecoration G active t → t.InputEdge → G := by
  classical
  exact fun {c} t => match t with
  | .leaf _ => fun _ e => nomatch e
  | .node g children => fun d e => match e with
    | ⟨i,none⟩ => if hi : active (S.argument g i) then d.1 ⟨i,hi⟩ else 1
    | ⟨i,some e⟩ => activeEdgeLabels active (children i) (d.2 i) e

def activeFromEdges (active : Component V → Prop) :
    {c : Component V} → (t : Tree S c) → (t.InputEdge → G) → ActiveDecoration G active t
  | _, .leaf _, _ => PUnit.unit
  | _, .node _ children, a =>
      (fun i => a ⟨i.val,none⟩, fun i => activeFromEdges active (children i) (fun e => a ⟨i,some e⟩))

theorem activeEdgeLabels_inactive (active : Component V → Prop)
    {c : Component V} (t : Tree S c) (d : ActiveDecoration G active t)
    (e : t.InputEdge) (he : ¬active (t.inputEdgeComponent e)) :
    activeEdgeLabels active t d e = 1 := by
  induction t with
  | leaf c => exact nomatch e
  | node g children ih =>
    rcases e with ⟨i,e⟩
    cases e with
    | none =>
      change ¬active (S.argument g i) at he
      simp only [activeEdgeLabels, dite_eq_right he]
    | some e => simpa only [activeEdgeLabels] using ih i (d.2 i) e he

theorem activeFromEdges_labels (active : Component V → Prop)
    {c : Component V} (t : Tree S c) (d : ActiveDecoration G active t) :
    activeFromEdges active t (activeEdgeLabels active t d) = d := by
  induction t with
  | leaf c => cases d; rfl
  | node g children ih =>
    apply Prod.ext
    · funext i
      simp only [activeFromEdges,activeEdgeLabels,dite_eq_left i.property]
    · funext i
      simpa only [activeFromEdges, activeEdgeLabels] using ih i (d.2 i)

theorem activeLabels_fromEdges (active : Component V → Prop)
    {c : Component V} (t : Tree S c) (a : t.InputEdge → G)
    (inactive : ∀ e, ¬active (t.inputEdgeComponent e) → a e = 1) :
    activeEdgeLabels active t (activeFromEdges active t a) = a := by
  classical
  induction t with
  | leaf c => funext e; exact nomatch e
  | node g children ih =>
    funext e
    rcases e with ⟨i,e⟩
    cases e with
    | none =>
      by_cases hi : active (S.argument g i)
      · simp only [activeEdgeLabels,activeFromEdges,dite_eq_left hi]
      · simp only [activeEdgeLabels,activeFromEdges,dite_eq_right hi]
        exact (inactive ⟨i,none⟩ hi).symm
    | some e =>
      simpa only [activeEdgeLabels, activeFromEdges] using congrFun (ih i (fun e => a ⟨i,some e⟩)
        (fun e he => inactive ⟨i,some e⟩ he)) e

theorem activeEvaluate_eq_path (active : Component V → Prop)
    (hs : Tree.ActiveSignature (S := S) active) {c : Component V}
    (t : Tree S c) (d : ActiveDecoration G active t) (l : Tree.ActiveLeaf t active) :
    activeEvaluate active hs t d l =
      JointArrayLifting.eval (activeEdgeLabels active t d) (t.leafPath l.val) := by
  induction t with
  | leaf c => rfl
  | node g children ih =>
    rcases l with ⟨⟨i,l⟩,hl⟩
    have hi : active (S.argument g i) :=
      (Tree.active_root_iff_leaf active hs (children i)).mpr ⟨l,hl⟩
    change d.1 ⟨i,hi⟩ * activeEvaluate active hs (children i) (d.2 i) ⟨l,hl⟩ = _
    rw [ih i (d.2 i) ⟨l,hl⟩]
    simp only [Tree.leafPath, JointArrayLifting.eval, List.map_cons, List.prod_cons,
      List.map_map, Function.comp_def, activeEdgeLabels, dite_eq_left hi]

/-- The concrete recovered graph fragment inherits the positive all-depth
rank-sensitive decoder, including its inactive and empty occurrences. -/
theorem graph_active_exact_decoder {K : Type*} [Group K] (h : G →* K)
    {c : Component GraphCut.Interface} (t : GraphCut.CutTree c)
    (x : Tree.ActiveLeaf t GraphCut.active → G)
    (d : ActiveDecoration G GraphCut.active t) :
    ObsEq h x (activeEvaluate GraphCut.active GraphCut.cutSignature_active t d) ↔
      ∃ e : ActiveDecoration G GraphCut.active t,
        ActiveDecorationEq h GraphCut.active t e d ∧
        activeEvaluate GraphCut.active GraphCut.cutSignature_active t e = x :=
  active_exact_tree_decoder h GraphCut.active GraphCut.cutSignature_active t x d

end RankSensitiveCompression
