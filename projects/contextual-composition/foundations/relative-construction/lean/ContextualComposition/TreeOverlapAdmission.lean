module

public import ContextualComposition.AllCouplings
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! Tree-overlap admission on an arbitrary finite simple tree. A span can be read in either direction; its matching equation has the same extension after reversing the endpoints. Raw tuples carry precisely the overlap equations. -/

@[expose] public section

namespace ContextualComposition.TreeOverlapAdmission

open CategoryTheory CouplingPullbacks
universe u
variable {V : Type u} (F : Type u ⥤ Type u)

structure Boundary (X Y : Type u) where
  carrier : Type u
  src : X → carrier
  dst : Y → carrier

structure Diagram (V : Type u) where
  graph : SimpleGraph V
  space : V → Type u
  edge : ∀ {v w}, graph.Adj v w → Boundary (space v) (space w)
  reverse : ∀ {v w} (a : graph.Adj v w) (x y), (edge a).src x = (edge a).dst y →
    (edge a.symm).src y = (edge a.symm).dst x

/-- Instantiate a single carrier for each actual undirected edge and arbitrary endpoint maps. Reversing the span asks for no additional constraint on the maps. -/
def ofEdges (G : SimpleGraph V) (X : V → Type u) (S : G.edgeSet → Type u)
    (leg : ∀ {i j} (h : G.Adj i j), X i → S ⟨s(i,j),h⟩) : Diagram V where
  graph := G
  space := X
  edge {i j} e := {
    carrier := S ⟨s(i,j),e⟩
    src := leg e
    dst := fun y => cast (congrArg S (Subtype.ext Sym2.eq_swap)) (leg e.symm y) }
  reverse {i j} e x y h := by
    change leg e x = cast _ (leg e.symm y) at h
    change leg e.symm y = cast _ (leg e x)
    rw [h]; simp

variable (D : Diagram V)

def Diagram.induce (s : Set V) : Diagram s where
  graph := D.graph.induce s
  space v := D.space v.val
  edge e := D.edge e
  reverse e := D.reverse e

abbrev Raw := {t : ∀ v, D.space v // ∀ {v w} (a : D.graph.Adj v w), (D.edge a).src (t v) = (D.edge a).dst (t w)}
def coord (v : V) (t : Raw D) := t.val v

def restrict (s : Set V) (t : Raw D) : Raw (D.induce s) :=
  ⟨fun v => t.val v.val, fun e => t.property e⟩

def Compatible (p : ∀ v, F.obj (D.space v)) :=
  ∀ {v w} (a : D.graph.Adj v w), push F (D.edge a).src (p v) = push F (D.edge a).dst (p w)

def Joint (p : ∀ v, F.obj (D.space v)) :=
  {q : F.obj (Raw D) // ∀ v, push F (coord D v) q = p v}

theorem necessary (p : ∀ v, F.obj (D.space v)) (q : Joint F D p) : Compatible F D p := by
  intro v w e
  rw [← q.property v, ← q.property w, push_push, push_push]
  exact congrArg (fun f => push F f q.val) (funext fun t => t.property e)

section Leaf

variable (v w : V) (adj : D.graph.Adj v w) (uniqueAdj : ∀ j, D.graph.Adj v j → j = w)

abbrev Rest := ({v}ᶜ : Set V)

private def extend [DecidableEq V] (t : Raw (D.induce (Rest v))) (x : D.space v) (i : V) : D.space i :=
  if eq : i = v then eq.symm ▸ x else t.val ⟨i,eq⟩

include adj uniqueAdj

private theorem extend_meets [DecidableEq V] (t : Raw (D.induce (Rest v))) (x : D.space v)
    (eq : (D.edge adj).src x = (D.edge adj).dst (t.val ⟨w, adj.ne.symm⟩)) :
    ∀ {i j} (e : D.graph.Adj i j), (D.edge e).src (extend D v t x i) = (D.edge e).dst (extend D v t x j) := by
  intro i j e
  by_cases hi : i = v
  · subst i
    obtain rfl := uniqueAdj j e
    simpa [extend, e.ne.symm] using eq
  · by_cases hj : j = v
    · subst j
      obtain rfl := uniqueAdj i e.symm
      simpa [extend, hi] using D.reverse adj x (t.val ⟨_,hi⟩) eq
    · simpa [extend, hi, hj, Diagram.induce] using (t.property (show (D.induce (Rest v)).graph.Adj ⟨i,hi⟩ ⟨j,hj⟩ from e))

theorem attach_leaf (weak : WeakPullbacks F) (p : ∀ i, F.obj (D.space i)) (ok : Compatible F D p)
    (q : Joint F (D.induce (Rest v)) (fun i => p i.val)) : Nonempty (Joint F D p) := by
  classical
  let old := D.induce (Rest v)
  let n : Rest v := ⟨w, adj.ne.symm⟩
  let f := (D.edge adj).dst ∘ coord old n
  let g := (D.edge adj).src
  have h : push F f q.val = push F g (p v) :=
    (push_push F (coord old n) (D.edge adj).dst q.val).symm.trans
      ((congrArg (push F (D.edge adj).dst) (q.property n)).trans (ok adj).symm)
  let build (z : PB f g) : Raw D := ⟨extend D v z.val.1 z.val.2,
    extend_meets D v w adj uniqueAdj _ _ z.property.symm⟩
  have hl : restrict D (Rest v) ∘ build = left := by
    funext z; apply Subtype.ext; funext i
    have hi : i.val ≠ v := i.property
    simp [restrict,build,extend,hi,left]
  have hr : coord D v ∘ build = right := by funext z; simp [coord,build,extend,right]
  obtain ⟨s,hs,hv⟩ := AllCouplings.glue F weak f g (restrict D (Rest v)) (coord D v) build hl hr q.val (p v) h
  refine ⟨s, fun i => ?_⟩
  by_cases hi : i = v
  · subst i; exact hv
  · exact (AllCouplings.marginal F _ (coord old ⟨i,hi⟩) (coord D i) rfl hs).trans (q.property ⟨i,hi⟩)

end Leaf

private theorem one_vertex [Subsingleton V] (v : V) (p : ∀ i, F.obj (D.space i)) : Nonempty (Joint F D p) := by
  let make (x : D.space v) : Raw D := ⟨fun i => Subsingleton.elim v i ▸ x, fun {i j} e => False.elim (e.ne (Subsingleton.elim i j))⟩
  refine ⟨push F make (p v), fun i => ?_⟩
  obtain rfl := Subsingleton.elim i v
  exact (push_push F make (coord D i) (p i)).trans (push_id F _)

private theorem tree_induction (weak : WeakPullbacks F) (n : ℕ) :
    ∀ {I : Type u} [Fintype I] (d : Diagram I) (_ : Fintype.card I = n) (_ : d.graph.IsTree)
      (p : ∀ i, F.obj (d.space i)), Compatible F d p → Nonempty (Joint F d p) := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro I _ d hn tree p ok
    cases subsingleton_or_nontrivial I with
    | inl s =>
      let := s
      exact one_vertex F d tree.connected.nonempty.some p
    | inr nt =>
      let := nt
      obtain ⟨v, hv⟩ := tree.exists_vert_degree_one_of_nontrivial
      obtain ⟨w, adj, uniqueAdj⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hv
      have ht : (d.induce (Rest v)).graph.IsTree :=
        ⟨tree.connected.induce_compl_singleton_of_degree_eq_one hv, tree.isAcyclic.induce _⟩
      have lt : Fintype.card (Rest v) < n := by
        rw [← hn]
        exact Fintype.card_subtype_lt (show ¬ v ∈ Rest v by simp [Rest])
      obtain ⟨q⟩ := ih _ lt (d.induce (Rest v)) rfl ht (fun i => p i.val) (fun e => ok e)
      exact attach_leaf F d v w adj uniqueAdj weak p ok q

/-- On every finite nonempty tree, edge compatibility is equivalent to a joint lift on the entire raw compatible-tuple space. -/
theorem admission [Fintype V] (weak : WeakPullbacks F) (tree : D.graph.IsTree) (p : ∀ v, F.obj (D.space v)) :
    Compatible F D p ↔ Nonempty (Joint F D p) :=
  ⟨tree_induction F weak _ D rfl tree p, fun ⟨q⟩ => necessary F D p q⟩

end ContextualComposition.TreeOverlapAdmission
