module
public import ContextualComposition.TreeOverlapAdmission

/-! A polynomial occurrence body on the entire raw tree overlap, constructed from compatible component bodies. Shape and position data are retained independently of the choice of a joint effect. -/

@[expose] public section
namespace ContextualComposition.JointOccurrenceAdmission
open CategoryTheory CouplingPullbacks TreeOverlapAdmission
set_option backward.isDefEq.respectTransparency false

universe u
structure Polynomial where
  Shape : Type u
  Pos : Shape → Type u

variable (S : Polynomial.{u}) {X Y Z V : Type u}
abbrev Body (X : Type u) := Σ s : S.Shape, S.Pos s → X
def map (f : X → Y) (q : Body S X) : Body S Y := ⟨q.1,f ∘ q.2⟩
def atPos {s : S.Shape} (q : Body S X) (h : s = q.1) (i : S.Pos s) := q.2 (h ▸ i)

theorem read_match {f : X → Z} {g : Y → Z} {a : Body S X} {b : Body S Y}
    (h : map S f a = map S g b) {s} (ha : s = a.1) (hb : s = b.1) (i : S.Pos s) :
    f (atPos S a ha i) = g (atPos S b hb i) := by
  have aux (m n : Body S Z) (e : m = n) (hm : s = m.1) (hn : s = n.1) : atPos S m hm i = atPos S n hn i := by
    subst n; rfl
  exact aux _ _ h ha hb

theorem body_ext (a b : Body S X) (h : a.1 = b.1) (p : ∀ i, a.2 i = atPos S b h i) : a = b := by
  obtain ⟨x,ax⟩ := a
  obtain ⟨y,by'⟩ := b
  change x = y at h
  subst y
  exact congrArg (Sigma.mk x) (funext p)

variable (D : Diagram V)
def diagram : Diagram V where
  graph := D.graph
  space v := Body S (D.space v)
  edge a := ⟨Body S (D.edge a).carrier,map S (D.edge a).src,map S (D.edge a).dst⟩
  reverse {v w} edge a b h := by
    have hs : a.1 = b.1 := congrArg Sigma.fst h
    apply body_ext S _ _ hs.symm
    intro j
    apply D.reverse edge
    exact read_match S h hs.symm rfl j

def project (q : Body S (Raw D)) : Raw (diagram S D) :=
  ⟨fun v => map S (coord D v) q,fun edge => body_ext S _ _ rfl (fun i => (q.2 i).property edge)⟩

theorem common_shape (conn : D.graph.Connected) (q : Raw (diagram S D)) (v w : V) :
    (q.val v).1 = (q.val w).1 := by
  obtain ⟨walk⟩ := conn.preconnected v w
  induction walk with
  | nil => rfl
  | cons edge _ ih => exact (congrArg Sigma.fst (q.property edge)).trans ih

noncomputable def assemble (conn : D.graph.Connected) (q : Raw (diagram S D)) : Body S (Raw D) :=
  let v := conn.nonempty.some
  ⟨(q.val v).1,fun j =>
    ⟨fun w => atPos S (q.val w) (common_shape S D conn q v w) j,
     fun edge => read_match S (q.property edge) _ _ j⟩⟩

theorem project_assemble (conn : D.graph.Connected) (q : Raw (diagram S D)) :
    project S D (assemble S D conn q) = q := by
  apply Subtype.ext
  funext v
  apply body_ext S _ _ (common_shape S D conn q conn.nonempty.some v)
  intro _; rfl

theorem assemble_project (conn : D.graph.Connected) (q : Body S (Raw D)) :
    assemble S D conn (project S D q) = q := by
  apply body_ext S _ _ rfl
  intro i
  apply Subtype.ext
  funext v
  rfl

noncomputable def bodyEquiv (conn : D.graph.Connected) : Body S (Raw D) ≃ Raw (diagram S D) :=
  ⟨project S D,assemble S D conn,assemble_project S D conn,project_assemble S D conn⟩

variable (F : Type u ⥤ Type u)

/-- The component witness fibres and bodies at one fixed compatible state. -/
structure Layer where
  witness : V → Type u
  effect : ∀ v, F.obj (witness v)
  body : ∀ v, witness v → Body S (D.space v)

variable {S D F} (L : Layer S D F)

def witnesses : Diagram V where
  graph := D.graph
  space := L.witness
  edge {v w} e := ⟨((diagram S D).edge e).carrier,((diagram S D).edge e).src ∘ L.body v,
    ((diagram S D).edge e).dst ∘ L.body w⟩
  reverse e _ _ h := (diagram S D).reverse e _ _ h

def componentBodies (z : Raw (witnesses L)) : Raw (diagram S D) :=
  ⟨fun v => L.body v (z.val v), fun edge => z.property edge⟩

def BoundaryAgreement := Compatible F (witnesses L) L.effect

structure JointStep where
  carrier : Type u
  effect : F.obj carrier
  leg : ∀ v, carrier → L.witness v
  body : carrier → Body S (Raw D)
  marginal : ∀ v, push F (leg v) effect = L.effect v
  native : ∀ v z, map S (coord D v) (body z) = L.body v (leg v z)

noncomputable def canonicalStep (conn : D.graph.Connected) (q : Joint F (witnesses L) L.effect) : JointStep L where
  carrier := Raw (witnesses L)
  effect := q.val
  leg := coord (witnesses L)
  body z := assemble S D conn (componentBodies L z)
  marginal := q.property
  native v z := congrArg (fun t : Raw (diagram S D) => t.val v) (project_assemble S D conn (componentBodies L z))

theorem necessary (s : JointStep L) : BoundaryAgreement L := by
  intro v w edge
  rw [← s.marginal v, ← s.marginal w,push_push,push_push]
  apply congrArg (fun k => push F k s.effect)
  funext z
  change map S (D.edge edge).src (L.body v (s.leg v z)) = map S (D.edge edge).dst (L.body w (s.leg w z))
  rw [← s.native,← s.native]
  exact (project S D (s.body z)).property edge

theorem admission [Fintype V] (tree : D.graph.IsTree) (weak : WeakPullbacks F) :
    BoundaryAgreement L ↔ Nonempty (JointStep L) := by
  refine ⟨fun h => ?_, fun ⟨s⟩ => necessary L s⟩
  obtain ⟨q⟩ := (TreeOverlapAdmission.admission F (witnesses L) weak tree L.effect).mp h
  exact ⟨canonicalStep L tree.connected q⟩

end ContextualComposition.JointOccurrenceAdmission
