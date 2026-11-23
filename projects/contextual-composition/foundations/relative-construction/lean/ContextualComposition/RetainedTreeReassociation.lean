module

public import ContextualComposition.TreeOverlapAdmission

/-! Retained reassociation on canonical tuple carriers. A finite binary decomposition partitions its vertex set down to singleton leaves. The uniqueness argument works for all such partitions, in particular the connected-subtree splits in the source. Admission is independent and uses the tree hypothesis. -/

@[expose] public section
noncomputable section

namespace ContextualComposition.RetainedTreeReassociation

open CategoryTheory CouplingPullbacks TreeOverlapAdmission
universe u
variable {V : Type u} (F : Type u ⥤ Type u) (D : Diagram V) (p : ∀ v, F.obj (D.space v))

inductive Cut (V : Type u) : Set V → Type u where
  | leaf (v : V) : Cut V {v}
  | split {s t : Set V} (l : Cut V s) (r : Cut V t) (separate : Disjoint s t) : Cut V (s ∪ t)

abbrev Tuple (s : Set V) := Raw (D.induce s)
abbrev Marginals (s : Set V) (q : F.obj (Tuple D s)) :=
  ∀ i : s, push F (coord (D.induce s) i) q = p i.val

def narrow {s t : Set V} (h : s ⊆ t) (x : Tuple D t) : Tuple D s :=
  ⟨fun i => x.val ⟨i.val,h i.property⟩,fun {i j} e => x.property
    (show (D.induce t).graph.Adj ⟨i.val,h i.property⟩ ⟨j.val,h j.property⟩ from e)⟩

theorem narrow_coord {s t : Set V} (h : s ⊆ t) (q : F.obj (Tuple D t)) (i : s) :
    push F (coord (D.induce s) i) (push F (narrow D h) q) = push F (coord (D.induce t) ⟨i.val,h i.property⟩) q :=
  push_push F _ _ _

/-- Child laws are stored as independent data, together with equations to their parent's actual marginals. -/
structure Checked (condition : Prop) : Type u where
  proof : condition

instance {h : Prop} : Subsingleton (Checked.{u} h) := ⟨fun ⟨_⟩ ⟨_⟩ => rfl⟩

def DataAt : {s : Set V} → Cut V s → F.obj (Tuple D s) → Type u
  | _, .leaf _, q => Checked.{u} (Marginals F D p _ q)
  | _, .split (s:=s) (t:=t) l r _, q =>
    {n : (Σ a, DataAt l a) // n.1 = push F (narrow D (Set.subset_union_left (t := t))) q} ×
    {n : (Σ a, DataAt r a) // n.1 = push F (narrow D (Set.subset_union_right (s := s))) q}

private theorem child_unique {K : Type u} {L : K → Type u} (sub : ∀ k, Subsingleton (L k)) (q : K) :
    Subsingleton {n : (Σ a, L a) // n.1 = q} := by
  constructor
  rintro ⟨⟨a, h⟩, rfl⟩ ⟨⟨b,k⟩,e⟩
  cases e
  cases (sub a).elim h k
  rfl

theorem data_determined {s : Set V} (c : Cut V s) : ∀ q, Subsingleton (DataAt F D p c q) := by
  induction c with
  | leaf => intro q; exact inferInstanceAs (Subsingleton (Checked _))
  | split l r _ il ir =>
    intro q
    constructor
    intro a b
    exact Prod.ext ((child_unique il _).elim a.1 b.1) ((child_unique ir _).elim a.2 b.2)

def dataOfMarginals {s : Set V} (c : Cut V s) : (q : F.obj (Tuple D s)) → Marginals F D p s q → DataAt F D p c q := by
  induction c with
  | leaf => intro q h; exact ⟨h⟩
  | split l r _ il ir =>
    intro q h
    exact ⟨⟨⟨_,il _ (fun i => (narrow_coord F D _ q i).trans (h _))⟩, rfl⟩,
           ⟨⟨_,ir _ (fun i => (narrow_coord F D _ q i).trans (h _))⟩, rfl⟩⟩

theorem data_marginals {s : Set V} (c : Cut V s) : ∀ q, DataAt F D p c q → Marginals F D p s q := by
  induction c with
  | leaf => intro q d; exact d.proof
  | split l r _ il ir =>
    rintro q ⟨⟨⟨_,ld⟩,rfl⟩,⟨⟨_,rd⟩,rfl⟩⟩ i
    rcases i.property with hi | hi
    · exact (narrow_coord F D _ q ⟨i.val,hi⟩).symm.trans (il _ ld _)
    · exact (narrow_coord F D _ q ⟨i.val,hi⟩).symm.trans (ir _ rd _)

abbrev Retained {s : Set V} (c : Cut V s) := Σ q, DataAt F D p c q

/-- Forgetting intermediate laws is invertible exactly because their full parent law is retained. -/
def rootEquiv {s : Set V} (c : Cut V s) : Retained F D p c ≃ {q // Marginals F D p s q} where
  toFun d := ⟨d.1,data_marginals F D p c _ d.2⟩
  invFun q := ⟨q.val,dataOfMarginals F D p c q.val q.property⟩
  left_inv d := by
    obtain ⟨q,d⟩ := d
    exact congrArg (Sigma.mk q) ((data_determined F D p c q).elim _ d)
  right_inv _ := rfl

def reassoc {s : Set V} (c d : Cut V s) : Retained F D p c ≃ Retained F D p d :=
  (rootEquiv F D p c).trans (rootEquiv F D p d).symm

theorem retains_root {s} (c d : Cut V s) (x : Retained F D p c) : (reassoc F D p c d x).1 = x.1 := rfl

theorem reassoc_id {s} (c : Cut V s) (x : Retained F D p c) : reassoc F D p c c x = x :=
  (rootEquiv F D p c).symm_apply_apply x

/-- Every chain of changes of decomposition has the same action for fixed endpoints. -/
theorem reassoc_trans {s} (a b c : Cut V s) (x : Retained F D p a) :
    reassoc F D p b c (reassoc F D p a b x) = reassoc F D p a c x := by
  simp [reassoc]

theorem reassoc_pentagon {s} (a b c d e : Cut V s) (x : Retained F D p a) :
    reassoc F D p c e (reassoc F D p b c (reassoc F D p a b x)) =
      reassoc F D p d e (reassoc F D p a d x) := by simp only [reassoc_trans]

def fullRaw : Tuple D Set.univ ≃ Raw D where
  toFun x := ⟨fun i => x.val ⟨i,trivial⟩, fun {i j} e => x.property
    (show (D.induce Set.univ).graph.Adj ⟨i,trivial⟩ ⟨j,trivial⟩ from e)⟩
  invFun := restrict D Set.univ
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def fullJoint : {q // Marginals F D p Set.univ q} ≃ Joint F D p where
  toFun q := ⟨push F (fullRaw D) q.val, fun i => (push_push F _ _ _).trans (q.property ⟨i,trivial⟩)⟩
  invFun q := ⟨push F (fullRaw D).symm q.val, fun i => (push_push F _ _ _).trans (q.property i.val)⟩
  left_inv q := Subtype.ext ((push_push F _ _ _).trans (push_id F q.val))
  right_inv q := Subtype.ext ((push_push F _ _ _).trans (push_id F q.val))

noncomputable def full_root_equivalence (c : Cut V Set.univ) : Retained F D p c ≃ Joint F D p :=
  (rootEquiv F D p c).trans (fullJoint F D p)

/-- A map of labelled overlap diagrams on the same graph, with actual carrier and boundary maps and commuting overlap legs. -/
structure DiagramMap (D E : Diagram V) where
  adjacent : ∀ i j, D.graph.Adj i j ↔ E.graph.Adj i j
  vertex : ∀ i, D.space i → E.space i
  boundary : ∀ {i j} (a : E.graph.Adj i j), (D.edge ((adjacent i j).mpr a)).carrier → (E.edge a).carrier
  src : ∀ {i j} (a : E.graph.Adj i j) x, boundary a ((D.edge ((adjacent i j).mpr a)).src x) = (E.edge a).src (vertex i x)
  dst : ∀ {i j} (a : E.graph.Adj i j) y, boundary a ((D.edge ((adjacent i j).mpr a)).dst y) = (E.edge a).dst (vertex j y)

namespace DiagramMap

variable {D} {E G : Diagram V} (m : DiagramMap D E)

def identity (D : Diagram V) : DiagramMap D D where
  adjacent _ _ := Iff.rfl
  vertex _ := id
  boundary _ := id
  src _ _ := rfl
  dst _ _ := rfl

def thenMap (n : DiagramMap E G) : DiagramMap D G where
  adjacent i j := (m.adjacent i j).trans (n.adjacent i j)
  vertex i := n.vertex i ∘ m.vertex i
  boundary a := n.boundary a ∘ m.boundary ((n.adjacent _ _).mpr a)
  src a x := (congrArg (n.boundary a) (m.src _ x)).trans (n.src _ _)
  dst a y := (congrArg (n.boundary a) (m.dst _ y)).trans (n.dst _ _)

def tuple (s : Set V) (t : Tuple D s) : Tuple E s :=
  ⟨fun i => m.vertex i.val (t.val i), fun {i j} a =>
    (m.src a _).symm.trans ((congrArg (m.boundary a) (t.property
      (show (D.induce s).graph.Adj i j from (m.adjacent i.val j.val).mpr a))).trans (m.dst a _))⟩

theorem tuple_identity (s : Set V) : (identity D).tuple s = id := rfl
theorem tuple_comp (n : DiagramMap E G) (s : Set V) : (m.thenMap n).tuple s = n.tuple s ∘ m.tuple s := rfl

theorem tuple_narrow {s t : Set V} (h : s ⊆ t) :
    m.tuple s ∘ narrow D h = narrow E h ∘ m.tuple t := rfl

variable {p} {r : ∀ i, F.obj (E.space i)}

theorem map_marginals (hp : ∀ i, push F (m.vertex i) (p i) = r i) {s} {q : F.obj (Tuple D s)}
    (h : Marginals F D p s q) : Marginals F E r s (push F (m.tuple s) q) :=
  fun i => (push_push F _ _ _).trans ((push_push F (coord (D.induce s) i) (m.vertex i.val) q).symm.trans
    ((congrArg (push F (m.vertex i.val)) (h i)).trans (hp i.val)))

/-- Map each stored child law on its own raw tuple carrier. -/
def mapData (hp : ∀ i, push F (m.vertex i) (p i) = r i) {s} (c : Cut V s) :
    (q : F.obj (Tuple D s)) → DataAt F D p c q → DataAt F E r c (push F (m.tuple s) q) := by
  induction c with
  | leaf => intro q d; exact ⟨m.map_marginals F hp d.proof⟩
  | split l r _ il ir =>
    rintro q ⟨⟨⟨_,ld⟩,rfl⟩,⟨⟨_,rd⟩,rfl⟩⟩
    have commute {s t : Set V} (h : s ⊆ t) (z : F.obj (Tuple D t)) :
        push F (m.tuple s) (push F (narrow D h) z) = push F (narrow E h) (push F (m.tuple t) z) := by
      rw [push_push, push_push, tuple_narrow]
    exact ⟨⟨⟨_,il _ ld⟩,commute _ q⟩,⟨⟨_,ir _ rd⟩,commute _ q⟩⟩

def mapRetained (hp : ∀ i, push F (m.vertex i) (p i) = r i) {s} (c : Cut V s) (x : Retained F D p c) :
    Retained F E r c := ⟨push F (m.tuple s) x.1,m.mapData F hp c x.1 x.2⟩

theorem reassoc_natural (hp : ∀ i, push F (m.vertex i) (p i) = r i) {s} (c d : Cut V s) (x : Retained F D p c) :
    m.mapRetained F hp d (reassoc F D p c d x) = reassoc F E r c d (m.mapRetained F hp c x) := by
  apply (rootEquiv F E r d).injective
  exact Subtype.ext rfl

end DiagramMap

end ContextualComposition.RetainedTreeReassociation
