module
public import ContextualComposition.OccurrenceFubini
public import ContextualComposition.JointOccurrenceSystem

/-! Finite native prefix maps for systems with a polynomial occurrence body. Each level retains its entire preceding raw prefix and one new witness per addressed occurrence. -/

@[expose] public section
noncomputable section
namespace ContextualComposition.GuardedOccurrencePrefixes
open CategoryTheory CouplingPullbacks JointOccurrenceAdmission JointOccurrenceSystem DependentConeInterchange
set_option backward.isDefEq.respectTransparency false

universe u
variable (T : CategoryTheory.Monad (Type u)) {X Y : Type u} (P S : Polynomial.{u})

class Finitary (S : Polynomial.{u}) : Prop where
  finite : ∀ s, Finite (S.Pos s)
attribute [instance] Finitary.finite

def one : Polynomial.{u} := ⟨PUnit,fun _ => PUnit⟩
def extend : Polynomial.{u} := ⟨Σ t : P.Shape, P.Pos t → S.Shape,fun t => Σ i, S.Pos (t.2 i)⟩

instance : Finitary (one.{u}) := ⟨fun _ => inferInstanceAs (Finite PUnit)⟩
instance [Finitary P] [Finitary S] : Finitary (extend P S) where
  finite t := inferInstanceAs (Finite (Σ i : P.Pos t.1, S.Pos (t.2 i)))

def power : Nat → Polynomial.{u}
  | 0 => one
  | n+1 => extend (power n) S

instance [Finitary S] (n : Nat) : Finitary (power S n) := by
  induction n with
  | zero => exact inferInstanceAs (Finitary one)
  | succ n ih => exact inferInstanceAs (Finitary (extend (power S n) S))

/-- Parent shape and all child shapes are retained; positions are dependent parent/child pairs. -/
def expand (q : Body P (Body S X)) : Body (extend P S) X :=
  ⟨⟨q.1,fun i => (q.2 i).1⟩,fun j => (q.2 j.1).2 j.2⟩

def unexpand (q : Body (extend P S) X) : Body P (Body S X) :=
  ⟨q.1.1,fun i => ⟨q.1.2 i,fun j => q.2 ⟨i,j⟩⟩⟩

def addressEquiv : Body P (Body S X) ≃ Body (extend P S) X :=
  ⟨expand P S,unexpand P S,fun _ => rfl,fun _ => rfl⟩

structure Stage (T : CategoryTheory.Monad (Type u)) (P : Polynomial.{u}) (X : Type u) where
  raw : Type u
  law : T.obj raw
  frontier : raw → Body P X

variable {T P S}
abbrev Assign (A : System T.toFunctor S X) (q : Body P X) := ∀ i, A.witness (q.2 i)

def sample [Finitary P] (A : System T.toFunctor S X) (q : Body P X) : T.obj (Assign A q) :=
  OccurrenceFubini.product T (fun i => A.effect (q.2 i))

def advance (A : System T.toFunctor S X) (q : Body P X) (w : Assign A q) : Body (extend P S) X :=
  expand P S ⟨q.1,fun i => A.output (q.2 i) (w i)⟩

def extendStage [Finitary P] (A : System T.toFunctor S X) (p : Stage T P X) : Stage T (extend P S) X where
  raw := Σ t, Assign A (p.frontier t)
  law := bind T p.law (fun t => push T.toFunctor (Sigma.mk t) (sample A (p.frontier t)))
  frontier z := advance A (p.frontier z.1) z.2

structure StageMap (p : Stage T P X) (q : Stage T P Y) (h : X → Y) where
  run : p.raw → q.raw
  marginal : push T.toFunctor run p.law = q.law
  body : ∀ t, map P h (p.frontier t) = q.frontier (run t)

variable {A : System T.toFunctor S X} {B : System T.toFunctor S Y} {h : X → Y}

def assignmentMap (f : NativeMap A B h) (q : Body P X) {t : Body P Y} (e : map P h q = t) :
    Assign A q → Assign B t := by
  subst t
  exact fun w i => f.onWitness (q.2 i) (w i)

theorem assignment_marginal [Finitary P] (f : NativeMap A B h) (q : Body P X) {t : Body P Y} (e : map P h q = t) :
    push T.toFunctor (assignmentMap f q e) (sample A q) = sample B t := by
  subst t
  exact (OccurrenceFubini.product_natural T (fun i => A.effect (q.2 i)) (fun i => f.onWitness (q.2 i))).trans
    (congrArg (OccurrenceFubini.product T) (funext fun i => f.marginal (q.2 i)))

theorem advance_map (f : NativeMap A B h) (q : Body P X) {t : Body P Y} (e : map P h q = t) (w : Assign A q) :
    map (extend P S) h (advance A q w) = advance B t (assignmentMap f q e w) := by
  subst t
  exact congrArg (fun labels => expand P S (⟨q.1,labels⟩ : Body P (Body S Y)))
    (funext fun i => f.body (q.2 i) (w i))

def advanceRaw {p : Stage T P X} {q : Stage T P Y} (f : NativeMap A B h) (g : StageMap p q h) :
    (Σ t, Assign A (p.frontier t)) → (Σ t, Assign B (q.frontier t)) :=
  fun z => ⟨g.run z.1,assignmentMap f _ (g.body z.1) z.2⟩

def extendMap [Finitary P] {p : Stage T P X} {q : Stage T P Y} (f : NativeMap A B h) (g : StageMap p q h) :
    StageMap (extendStage A p) (extendStage B q) h where
  run := advanceRaw f g
  body t := advance_map f (p.frontier t.1) (g.body t.1) t.2
  marginal := by
    change push T.toFunctor (advanceRaw f g) (bind T p.law _) = bind T q.law _
    rw [push_bind,← g.marginal,bind_push]
    apply congrArg (bind T p.law)
    funext t
    change push T.toFunctor (advanceRaw f g) (push T.toFunctor (Sigma.mk t) _) =
      push T.toFunctor (Sigma.mk (g.run t)) (sample B (q.frontier (g.run t)))
    rw [← assignment_marginal f (p.frontier t) (g.body t),push_push,push_push]
    rfl

theorem truncate [Finitary P] (aff : OccurrenceFubini.Affine T) (A : System T.toFunctor S X) (p : Stage T P X) :
    push T.toFunctor Sigma.fst (extendStage A p).law = p.law := by
  change push T.toFunctor Sigma.fst (bind T p.law _) = _
  rw [push_bind]
  apply Eq.trans _ (bind_ret T p.law)
  apply congrArg (bind T p.law)
  funext t
  rw [push_push]
  exact OccurrenceFubini.discard T aff _ t

def prefixes [Finitary S] (A : System T.toFunctor S X) (x : X) : (n : Nat) → Stage T (power S n) X
  | 0 => ⟨PUnit,ret T PUnit.unit,fun _ => ⟨PUnit.unit,fun _ => x⟩⟩
  | n+1 => extendStage A (prefixes A x n)

def prefixMap [Finitary S] (f : NativeMap A B h) (x : X) : (n : Nat) →
    StageMap (prefixes A x n) (prefixes B (h x) n) h
  | 0 => ⟨id,push_id T.toFunctor _,fun _ => rfl⟩
  | n+1 => extendMap f (prefixMap f x n)

def forgetLast [Finitary S] (A : System T.toFunctor S X) (x : X) (n : Nat) :
    (prefixes A x (n+1)).raw → (prefixes A x n).raw := Sigma.fst

theorem prefix_truncate [Finitary S] (aff : OccurrenceFubini.Affine T) (A : System T.toFunctor S X) (x : X) (n : Nat) :
    push T.toFunctor (forgetLast A x n) (prefixes A x (n+1)).law = (prefixes A x n).law :=
  truncate aff A (prefixes A x n)

theorem truncate_map [Finitary S] (f : NativeMap A B h) (x : X) (n : Nat) (t : (prefixes A x (n+1)).raw) :
    (prefixMap f x n).run (forgetLast A x n t) = forgetLast B (h x) n ((prefixMap f x (n+1)).run t) := rfl

def polynomialFunctor (S : Polynomial.{u}) : Type u ⥤ Type u where
  obj := Body S
  map f := TypeCat.ofHom (map S (fun x => f x))
  map_id _ := rfl
  map_comp _ _ := rfl

variable (M : CategoryTheory.Monad (Type u)) (presentation : polynomialFunctor S ⟶ M.toFunctor)

/-- Interpret every retained leaf through the polynomial body and flatten the resulting hierarchy with the content monad. -/
def flatten : (n : Nat) → {X : Type u} → Body (power S n) X → M.obj X
  | 0, _, q => ret M (q.2 PUnit.unit)
  | n+1, _, q => bind M (flatten n (unexpand (power S n) S q)) (fun b => presentation.app _ b)

theorem flatten_natural (n : Nat) (f : X → Y) (q : Body (power S n) X) :
    push M.toFunctor f (flatten M presentation n q) = flatten M presentation n (map (power S n) f q) := by
  induction n generalizing X Y with
  | zero => exact push_ret M _ _
  | succ n ih =>
    change push M.toFunctor f (bind M (flatten M presentation n _) _) =
      bind M (flatten M presentation n (map (power S n) (map S f) (unexpand (power S n) S q))) _
    rw [push_bind,← ih,bind_push]
    apply congrArg (bind M _)
    funext b
    exact (congrArg (fun (k : Body S X ⟶ M.obj Y) => k b) (presentation.naturality (TypeCat.ofHom f))).symm

theorem flattened_prefix_map [Finitary S] (f : NativeMap A B h) (x : X) (n : Nat) (t : (prefixes A x n).raw) :
    push M.toFunctor h (flatten M presentation n ((prefixes A x n).frontier t)) =
      flatten M presentation n ((prefixes B (h x) n).frontier ((prefixMap f x n).run t)) := by
  rw [flatten_natural,(prefixMap f x n).body]

/-- Specialize the inductive construction to the projections of the system assembled under the tree boundary equations. -/
def jointPrefixMap [Finitary S] {V : Type u} (D : TreeOverlapAdmission.Diagram V)
    (systems : ∀ v, System T.toFunctor S (D.space v)) (conn : D.graph.Connected)
    (q : Choices D systems) (v : V) (x : TreeOverlapAdmission.Raw D) (n : Nat) :=
  prefixMap (componentMap D systems conn q v) x n

end ContextualComposition.GuardedOccurrencePrefixes
