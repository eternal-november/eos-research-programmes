import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic
import TreeArrayBridge
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.TypeTags.Hom

/-! Rank-sensitive observations keep labels exactly on singleton active profiles
and keep only their homomorphic image on branching profiles. Empty profiles have
one label function. This file concerns coefficient data over one fixed old
skeleton; it does not identify old operations or identity guards. -/
set_option backward.isDefEq.respectTransparency false
namespace RankSensitiveCompression
universe u v w z
variable {G : Type u} {K : Type v} [Group G] [Group K]

def ObsEq (h : G →* K) {I : Type w} (a b : I → G) : Prop :=
  (Subsingleton I → a = b) ∧ ∀ i, h (a i) = h (b i)

theorem obs_refl (h : G →* K) {I : Type w} (a : I → G) : ObsEq h a a :=
  ⟨fun _ => rfl, fun _ => rfl⟩

theorem obs_symm (h : G →* K) {I : Type w} {a b : I → G}
    (hab : ObsEq h a b) : ObsEq h b a :=
  ⟨fun hs => (hab.1 hs).symm, fun i => (hab.2 i).symm⟩

theorem obs_trans (h : G →* K) {I : Type w} {a b c : I → G}
    (hab : ObsEq h a b) (hbc : ObsEq h b c) : ObsEq h a c :=
  ⟨fun hs => (hab.1 hs).trans (hbc.1 hs), fun i => (hab.2 i).trans (hbc.2 i)⟩

def graft {I : Type w} {J : I → Type z} (a : I → G)
    (b : (i : I) → J i → G) : (Sigma J) → G :=
  fun ij => a ij.1 * b ij.1 ij.2

lemma outer_subsingleton {I : Type w} {J : I → Type z}
    (nonerase : ∀ i, Nonempty (J i)) (hs : Subsingleton (Sigma J)) : Subsingleton I := by
  classical
  constructor
  intro i k
  exact congrArg Sigma.fst (hs.elim ⟨i, Classical.choice (nonerase i)⟩
    ⟨k, Classical.choice (nonerase k)⟩)

lemma child_subsingleton {I : Type w} {J : I → Type z}
    (hs : Subsingleton (Sigma J)) (i : I) : Subsingleton (J i) := by
  constructor
  intro j k
  exact Sigma.mk.inj_iff.mp (hs.elim ⟨i,j⟩ ⟨i,k⟩) |>.2 |> eq_of_heq

lemma total_subsingleton {I : Type w} {J : I → Type z}
    (hi : Subsingleton I) (i : I) (hj : Subsingleton (J i)) : Subsingleton (Sigma J) := by
  constructor
  intro x y
  rcases x with ⟨k,x⟩
  rcases y with ⟨l,y⟩
  have hk : k = i := hi.elim k i
  have hl : l = i := hi.elim l i
  subst k
  subst l
  exact congrArg (Sigma.mk i) (hj.elim x y)

/-- Nonerasing grafting descends through the rank-sensitive relation. -/
theorem graft_congr (h : G →* K) {I : Type w} {J : I → Type z}
    (nonerase : ∀ i, Nonempty (J i)) {a a' : I → G}
    {b b' : (i : I) → J i → G}
    (ha : ObsEq h a a') (hb : ∀ i, ObsEq h (b i) (b' i)) :
    ObsEq h (graft a b) (graft a' b') := by
  constructor
  · intro hs
    have ea := ha.1 (outer_subsingleton nonerase hs)
    have eb : b = b' := funext (fun i => (hb i).1 (child_subsingleton hs i))
    subst a'; subst b'; rfl
  · intro ij
    simp only [graft, map_mul, ha.2 ij.1, (hb ij.1).2 ij.2]

/-- Every prescribed whole factor-state tuple lifts at the exact concrete
source. The same parent is used for every descendant in its group. -/
theorem root_lift (h : G →* K) {I : Type w} {J : I → Type z}
    (nonerase : ∀ i, Nonempty (J i))
    (x : (Sigma J) → G) (a : I → G) (b : (i : I) → J i → G)
    (valid : ObsEq h x (graft a b)) :
    ∃ a' b', ObsEq h a' a ∧ (∀ i, ObsEq h (b' i) (b i)) ∧ graft a' b' = x := by
  classical
  by_cases hi : Subsingleton I
  · let b' : (i : I) → J i → G := fun i j => (a i)⁻¹ * x ⟨i,j⟩
    refine ⟨a, b', obs_refl h a, ?_, ?_⟩
    · intro i
      constructor
      · intro hj
        have ex := valid.1 (total_subsingleton hi i hj)
        funext j
        have ej := congrFun ex ⟨i,j⟩
        simp only [b', ej, graft, inv_mul_cancel_left]
      · intro j
        have ej := valid.2 ⟨i,j⟩
        simp only [b', map_mul, map_inv, ej, graft, map_mul, inv_mul_cancel_left]
    · funext ij
      simp only [graft, b', mul_inv_cancel_left]
  · let a' : I → G := fun i => if hj : Subsingleton (J i) then
        x ⟨i, Classical.choice (nonerase i)⟩ * (b i (Classical.choice (nonerase i)))⁻¹
      else a i
    let b' : (i : I) → J i → G := fun i j => (a' i)⁻¹ * x ⟨i,j⟩
    have ha' : ∀ i, h (a' i) = h (a i) := by
      intro i
      dsimp only [a']
      split_ifs with hj
      · have ej := valid.2 ⟨i, Classical.choice (nonerase i)⟩
        simp only [map_mul, map_inv, ej, graft, map_mul, mul_inv_cancel_right]
      · rfl
    refine ⟨a', b', ⟨fun hs => False.elim (hi hs), ha'⟩, ?_, ?_⟩
    · intro i
      constructor
      · intro hj
        funext j
        have jj := hj.elim (Classical.choice (nonerase i)) j
        simp only [b', a', dite_eq_left hj, jj]
        simp only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one]
      · intro j
        have ej := valid.2 ⟨i,j⟩
        simp only [b', map_mul, map_inv, ha' i, ej, graft, map_mul, inv_mul_cancel_left]
    · funext ij
      simp only [graft, b', mul_inv_cancel_left]

/-- On a singleton profile the true vertex-free identity test is reflected. -/
theorem unit_reflection (h : G →* K) {I : Type w} [Subsingleton I]
    {x : I → G} (hx : ObsEq h x (fun _ => 1)) : x = fun _ => 1 :=
  hx.1 inferInstance

/-- Empty profiles carry no coefficient information. -/
theorem empty_profile (h : G →* K) {I : Type w} [IsEmpty I] (a b : I → G) :
    ObsEq h a b := by
  have e : a = b := funext (fun i => isEmptyElim i)
  subst b
  exact obs_refl h a

section TypedTrees
open WitnessedDecompositions
variable {V : Type*} [Quiver V] {S : Signature V}

/-- Literal coefficient decorations keep the root tuple and every child tuple. -/
def Decoration (G : Type u) : {c : Component V} → Tree S c → Type u
  | _, .leaf _ => PUnit.{u+1}
  | _, .node g children => (Path.Slot (S.input g) → G) ×
      ((i : Path.Slot (S.input g)) → Decoration G (children i))

/-- Exact source coefficients obtained by composing all ancestor labels. -/
def evaluate : {c : Component V} → (t : Tree S c) →
    Decoration G t → Tree.Leaf t → G
  | _, .leaf _, _ => fun _ => 1
  | _, .node _ children, d => graft d.1 (fun i => evaluate (children i) (d.2 i))

/-- Convert recursive factor tuples to the same shared edge IDs used by the
uniform lifting kernel. No intermediate coefficient is dropped. -/
def edgeDecoration : {c : Component V} → (t : Tree S c) →
    Decoration G t → Tree.InputEdge t → G
  | _, .leaf _, _, e => nomatch e
  | _, .node g children, d, ⟨i, none⟩ => d.1 i
  | _, .node g children, d, ⟨i, some e⟩ => edgeDecoration (children i) (d.2 i) e

def fromEdgeDecoration : {c : Component V} → (t : Tree S c) →
    (Tree.InputEdge t → G) → Decoration G t
  | _, .leaf _, _ => PUnit.unit
  | _, .node g children, a => (fun i => a ⟨i,none⟩,
      fun i => fromEdgeDecoration (children i) (fun e => a ⟨i,some e⟩))

theorem edge_fromEdge {c : Component V} (t : Tree S c) (a : Tree.InputEdge t → G) :
    edgeDecoration t (fromEdgeDecoration t a) = a := by
  induction t with
  | leaf c => funext e; exact nomatch e
  | node g children ih =>
    funext e
    rcases e with ⟨i,e⟩
    cases e with
    | none => rfl
    | some e => exact congrFun (ih i (fun e => a ⟨i,some e⟩)) e

theorem fromEdge_edge {c : Component V} (t : Tree S c) (d : Decoration G t) :
    fromEdgeDecoration t (edgeDecoration t d) = d := by
  induction t with
  | leaf c => exact (show Subsingleton PUnit from inferInstance).elim _ _
  | node g children ih =>
    rcases d with ⟨a,b⟩
    change (a, fun i => fromEdgeDecoration (children i)
      (edgeDecoration (children i) (b i))) = (a,b)
    simp only [ih]

/-- The positive quotient and uniform no-go use identical path products. -/
theorem evaluate_eq_path {c : Component V} (t : Tree S c) (d : Decoration G t)
    (l : Tree.Leaf t) :
    evaluate t d l = JointArrayLifting.eval (edgeDecoration t d) (Tree.leafPath t l) := by
  induction t with
  | leaf c => rfl
  | node g children ih =>
    rcases l with ⟨i,l⟩
    simp only [evaluate, graft, Tree.leafPath, JointArrayLifting.eval,
      List.map_cons, List.prod_cons, edgeDecoration, List.map_map]
    exact congrArg (fun z => d.1 i * z) (ih i (d.2 i) l)

/-- Observations retain each actual factor occurrence, not merely the total. -/
def DecorationEq (h : G →* K) : {c : Component V} → (t : Tree S c) →
    Decoration G t → Decoration G t → Prop
  | _, .leaf _, _, _ => True
  | _, .node _ children, d, e => ObsEq h d.1 e.1 ∧
      ∀ i, DecorationEq h (children i) (d.2 i) (e.2 i)

/-- Every coefficient-bearing input has a final descendant. A nullary root
has no such input and remains allowed; a vertex-free leaf remains allowed. -/
def Nonerasing : {c : Component V} → (t : Tree S c) → Prop
  | _, .leaf _ => True
  | _, .node _ children => ∀ i, Nonempty (Tree.Leaf (children i)) ∧ Nonerasing (children i)

theorem evaluate_congr (h : G →* K) {c : Component V} (t : Tree S c)
    (live : Nonerasing t) {d e : Decoration G t} (hd : DecorationEq h t d e) :
    ObsEq h (evaluate t d) (evaluate t e) := by
  induction t with
  | leaf c => exact obs_refl h _
  | node g children ih =>
    exact graft_congr h (fun i => (live i).1) hd.1
      (fun i => ih i (live i).2 (hd.2 i))

/-- All-depth source-fixed lifting, including the literal vertex-free base.
No depth bound, finite enumeration, or assumed exact decoder is used. -/
theorem all_tree_lift (h : G →* K) {c : Component V} (t : Tree S c)
    (live : Nonerasing t) (x : Tree.Leaf t → G) (d : Decoration G t)
    (valid : ObsEq h x (evaluate t d)) :
    ∃ e : Decoration G t, DecorationEq h t e d ∧ evaluate t e = x := by
  induction t with
  | leaf c =>
    refine ⟨PUnit.unit, trivial, ?_⟩
    exact (valid.1 (show Subsingleton Unit from inferInstance)).symm
  | node g children ih =>
    obtain ⟨a, b, ha, hb, hx⟩ := root_lift h (fun i => (live i).1)
      x d.1 (fun i => evaluate (children i) (d.2 i)) valid
    have lifts : ∀ i, ∃ e : Decoration G (children i),
        DecorationEq h (children i) e (d.2 i) ∧ evaluate (children i) e = b i :=
      fun i => ih i (live i).2 (b i) (d.2 i) (hb i)
    classical
    choose es hes evals using lifts
    refine ⟨(a,es), ⟨ha,hes⟩, ?_⟩
    change graft a (fun i => evaluate (children i) (es i)) = x
    simpa only [evals] using hx

/-- Representative independence holds for entire arrays of factor observations. -/
theorem exact_tree_decoder (h : G →* K) {c : Component V} (t : Tree S c)
    (live : Nonerasing t) (x : Tree.Leaf t → G) (d : Decoration G t) :
    ObsEq h x (evaluate t d) ↔
      ∃ e : Decoration G t, DecorationEq h t e d ∧ evaluate t e = x := by
  constructor
  · exact all_tree_lift h t live x d
  · rintro ⟨e,he,hx⟩
    rw [← hx]
    exact evaluate_congr h t live he
end TypedTrees

/-- Concrete properness control: the cyclic-four-to-cyclic-two map. -/
def cyclicReduction : Multiplicative (ZMod 4) →* Multiplicative (ZMod 2) :=
  (ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)).toAddMonoidHom.toMultiplicative

def coarseLeft : Fin 2 → Multiplicative (ZMod 4) := fun _ => Multiplicative.ofAdd 0
def coarseRight : Fin 2 → Multiplicative (ZMod 4) :=
  fun i => Multiplicative.ofAdd (if i = 0 then 2 else 0)

theorem branching_proper_compression :
    ObsEq cyclicReduction coarseLeft coarseRight ∧ coarseLeft ≠ coarseRight := by
  constructor
  · constructor
    · intro hs
      have bad : (0 : Fin 2) = 1 := hs.elim 0 1
      exact False.elim ((by decide : (0 : Fin 2) ≠ 1) bad)
    · intro i
      fin_cases i <;> decide
  · intro he
    have e := congrFun he 0
    have ne : coarseLeft 0 ≠ coarseRight 0 := by decide
    exact ne e

end RankSensitiveCompression
