module
public import ContextualComposition.FiniteTelescope
public import Mathlib.CategoryTheory.Types.Basic
@[expose] public section
namespace ContextualComposition.FiniteTelescope.Reindex
open CategoryTheory
universe u v
variable {B : Type u} [Category.{v} B] {G : Span.{u,u} B}

/-- A chosen lift returns the new successor, the actual restricted grade, and the base map
on which the next grade (or terminal payload) must be restricted. -/
abbrev Lifted (G : Span.{u,u} B) (a b : B) := Σ c, G a c × (c ⟶ b)

def follow {a a' b} (r : ∀ {a a' b : B}, (a' ⟶ a) → G a b → Lifted G a' b)
    (f : a' ⟶ a) (z : Lifted G a b) : Lifted G a' b :=
  let y := r f z.2.1
  ⟨y.1,y.2.1,y.2.2 ≫ z.2.2⟩

/-- Split one-step restriction of grades with their extension maps. These are input laws
only on single grades; no telescope, iterated action or comparison law is supplied. -/
structure Split (G : Span.{u,u} B) where
  lift : ∀ {a a' b : B}, (a' ⟶ a) → G a b → Lifted G a' b
  lift_id : ∀ {a b} (g : G a b), lift (𝟙 a) g = ⟨b,g,𝟙 b⟩
  lift_comp : ∀ {a a' a'' b} (f : a'' ⟶ a') (k : a' ⟶ a) (g : G a b),
    lift (f ≫ k) g = follow (@lift) f (lift k g)

/-- Explicit Type-valued contravariant base action. -/
structure Family (B : Type u) [Category.{v} B] where
  obj : B → Type u
  res : ∀ {a b}, (a ⟶ b) → obj b → obj a
  res_id : ∀ {a} (x : obj a), res (𝟙 a) x = x
  res_comp : ∀ {a b c} (f : a ⟶ b) (k : b ⟶ c) (x : obj c), res (f ≫ k) x = res f (res k x)

variable (S : Split G) (X : Family B)
def stepRes {a a'} (f : a' ⟶ a) (z : Step G X.obj a) : Step G X.obj a' :=
  let y := S.lift f z.2.1
  ⟨y.1,y.2.1,X.res y.2.2 z.2.2⟩

theorem stepRes_id {a} (z : Step G X.obj a) : stepRes S X (𝟙 a) z = z := by
  rcases z with ⟨b,g,x⟩
  simp only [stepRes]; erw [S.lift_id g]; simp only [X.res_id]; rfl

theorem stepRes_comp {a a' a''} (f : a'' ⟶ a') (k : a' ⟶ a) (z : Step G X.obj a) :
    stepRes S X (f ≫ k) z = stepRes S X f (stepRes S X k z) := by
  rcases z with ⟨b,g,x⟩
  simp only [stepRes]; erw [S.lift_comp f k g]; simp only [follow, X.res_comp]; rfl

def stepFamily : Family B where
  obj := Step G X.obj
  res := stepRes S X
  res_id := stepRes_id S X
  res_comp := stepRes_comp S X

/-- Reindex an existing #167 iterate, recursing on the actual successor map, without
identifying the successor of the reindexed grade with the former successor. -/
def iterRes {a a'} (f : a' ⟶ a) (n : Nat) (z : Iter.{u,u,u} G X.obj n a) :
    Iter.{u,u,u} G X.obj n a' :=
  match n with
  | 0 => X.res f z
  | n+1 =>
    let y := S.lift f z.2.1
    ⟨y.1,y.2.1,iterRes y.2.2 n z.2.2⟩

theorem iterRes_id {a} (n : Nat) (z : Iter.{u,u,u} G X.obj n a) :
    iterRes S X (𝟙 a) n z = z := by
  induction n generalizing a with
  | zero => exact X.res_id z
  | succ n ih => rcases z with ⟨b,g,x⟩; simp only [iterRes]; erw [S.lift_id g]; simp only [ih]; rfl

theorem iterRes_comp {a a' a''} (f : a'' ⟶ a') (k : a' ⟶ a) (n : Nat)
    (z : Iter.{u,u,u} G X.obj n a) :
    iterRes S X (f ≫ k) n z = iterRes S X f n (iterRes S X k n z) := by
  induction n generalizing a a' a'' with
  | zero => exact X.res_comp f k z
  | succ n ih => rcases z with ⟨b,g,x⟩; simp only [iterRes]; erw [S.lift_comp f k g]; simp only [follow,ih]; rfl

def chainValue {a b a'} (f : a' ⟶ a) (p : Chain G a b) (x : X.obj b) : Value.{u,u,u} G X.obj a' :=
  match p with
  | .nil _ => ⟨a',.nil a',X.res f x⟩
  | .cons g q =>
    let y := S.lift f g
    let z := chainValue y.2.2 q x
    ⟨z.1,.cons y.2.1 z.2.1,z.2.2⟩

def valueRes {a a'} (f : a' ⟶ a) (z : Value.{u,u,u} G X.obj a) : Value.{u,u,u} G X.obj a' :=
  chainValue S X f z.2.1 z.2.2

def packedRes {a a'} (f : a' ⟶ a) (z : Σ n, Iter.{u,u,u} G X.obj n a) :
    Σ n, Iter.{u,u,u} G X.obj n a' := ⟨z.1,iterRes S X f z.1 z.2⟩

theorem pack_reindex {a b a'} (f : a' ⟶ a) (p : Chain G a b) (x : X.obj b) :
    extensionEquiv.{u,u,u} G X.obj a' (chainValue S X f p x) = packedRes S X f (pack.{u,u,u} p x) := by
  induction p generalizing a' with
  | nil => rfl
  | @cons i j b g p ih =>
    let y := S.lift f g
    exact congrArg (fun t : Σ n, Iter.{u,u,u} G X.obj n y.1 =>
      (⟨t.1+1,y.1,y.2.1,t.2⟩ : Σ n, Iter.{u,u,u} G X.obj n a')) (ih y.2.2 x)

theorem packedRes_id {a} (z : Σ n, Iter.{u,u,u} G X.obj n a) : packedRes S X (𝟙 a) z = z :=
  congrArg (Sigma.mk z.1) (iterRes_id S X z.1 z.2)

theorem packedRes_comp {a a' a''} (f : a'' ⟶ a') (k : a' ⟶ a) (z : Σ n, Iter.{u,u,u} G X.obj n a) :
    packedRes S X (f ≫ k) z = packedRes S X f (packedRes S X k z) :=
  congrArg (Sigma.mk z.1) (iterRes_comp S X f k z.1 z.2)

theorem valueRes_id {a} (z : Value.{u,u,u} G X.obj a) : valueRes S X (𝟙 a) z = z := by
  apply (extensionEquiv.{u,u,u} G X.obj a).injective
  exact (pack_reindex S X _ z.2.1 z.2.2).trans (packedRes_id S X _)

theorem valueRes_comp {a a' a''} (f : a'' ⟶ a') (k : a' ⟶ a) (z : Value.{u,u,u} G X.obj a) :
    valueRes S X (f ≫ k) z = valueRes S X f (valueRes S X k z) := by
  apply (extensionEquiv.{u,u,u} G X.obj a'').injective
  calc
    _ = packedRes S X (f ≫ k) (extensionEquiv G X.obj a z) := pack_reindex S X _ _ _
    _ = packedRes S X f (packedRes S X k (extensionEquiv G X.obj a z)) := packedRes_comp S X _ _ _
    _ = packedRes S X f (extensionEquiv G X.obj a' (valueRes S X k z)) :=
      congrArg (packedRes S X f) (pack_reindex S X k _ _).symm
    _ = _ := (pack_reindex S X f _ _).symm

def valueFamily : Family B where
  obj a := Value.{u,u,u} G X.obj a
  res := valueRes S X
  res_id := valueRes_id S X
  res_comp := valueRes_comp S X

def packedFamily : Family B where
  obj a := Σ n, Iter.{u,u,u} G X.obj n a
  res := packedRes S X
  res_id := packedRes_id S X
  res_comp := packedRes_comp S X

def Family.toPresheaf (P : Family B) : Bᵒᵖ ⥤ Type u where
  obj x := P.obj x.unop
  map f := TypeCat.ofHom (P.res f.unop)
  map_id _ := by ext x; exact P.res_id x
  map_comp f k := by ext x; exact P.res_comp k.unop f.unop x

def Family.ofPresheaf (P : Bᵒᵖ ⥤ Type u) : Family B where
  obj x := P.obj (.op x)
  res f x := (P.map f.op) x
  res_id x := by change (P.map (𝟙 _)) x = x; rw [P.map_id]; rfl
  res_comp f k x := by change (P.map (k.op ≫ f.op)) x = _; rw [P.map_comp]; rfl

/-- The actual #167 comparison is an isomorphism of presheaves of types over the non-discrete base. -/
def baseComparison : (valueFamily S X).toPresheaf ≅ (packedFamily S X).toPresheaf :=
  NatIso.ofComponents (fun a => (extensionEquiv.{u,u,u} G X.obj a.unop).toIso) (by
    intro a b f
    ext z
    exact pack_reindex S X f.unop z.2.1 z.2.2)

theorem unpack_reindex {a a'} (f : a' ⟶ a) (n : Nat) (z : Iter.{u,u,u} G X.obj n a) :
    unpack.{u,u,u} n (iterRes S X f n z) = valueRes S X f (unpack.{u,u,u} n z) := by
  exact congrArg (fun k : (packedFamily S X).obj a ⟶ (valueFamily S X).obj a' => k ⟨n,z⟩)
    ((baseComparison S X).inv.naturality f.op)

theorem valueRes_empty {a a'} (f : a' ⟶ a) (x : X.obj a) :
    valueRes S X f (emptyValue.{u,u,u} x) = emptyValue (X.res f x) := rfl

theorem valueRes_singleton {a a' b} (f : a' ⟶ a) (g : G a b) (x : X.obj b) :
    valueRes S X f ⟨b,singleton g,x⟩ =
      (let y := S.lift f g; ⟨y.1,singleton y.2.1,X.res y.2.2 x⟩) := rfl

theorem restriction_preserves_length {a b a'} (f : a' ⟶ a) (p : Chain G a b) (x : X.obj b) :
    length (chainValue S X f p x).2.1 = length p := by
  induction p generalizing a' with
  | nil => rfl
  | cons g p ih => exact congrArg Nat.succ (ih (S.lift f g).2.2 x)

/-- Payload changes must be natural with respect to the actual base arrows. -/
theorem chain_payload {Y : Family B} (τ : X.toPresheaf ⟶ Y.toPresheaf)
    {a b a'} (f : a' ⟶ a) (p : Chain G a b) (x : X.obj b) :
    valueMap.{u,u,u} (fun c => (τ.app (.op c))) (chainValue S X f p x) =
      chainValue S Y f p ((τ.app (.op b)) x) := by
  induction p generalizing a' with
  | nil b =>
    exact congrArg (fun y : Y.obj a' => (⟨a',.nil a',y⟩ : Value.{u,u,u} G Y.obj a'))
      (congrArg (fun k : X.obj b ⟶ Y.obj a' => k x) (τ.naturality f.op))
  | @cons i j b g p ih =>
    let y := S.lift f g
    exact congrArg (fun z : Value.{u,u,u} G Y.obj y.1 =>
      (⟨z.1,.cons y.2.1 z.2.1,z.2.2⟩ : Value.{u,u,u} G Y.obj a')) (ih y.2.2 x)

def valuePayload {Y : Family B} (τ : X.toPresheaf ⟶ Y.toPresheaf) :
    (valueFamily S X).toPresheaf ⟶ (valueFamily S Y).toPresheaf where
  app a := TypeCat.ofHom (valueMap.{u,u,u} (fun c => τ.app (.op c)))
  naturality _ _ f := by ext z; exact chain_payload S X τ f.unop z.2.1 z.2.2

theorem iter_payload {Y : Family B} (τ : X.toPresheaf ⟶ Y.toPresheaf)
    {a a'} (f : a' ⟶ a) (n : Nat) (z : Iter.{u,u,u} G X.obj n a) :
    iterMap.{u,u,u} (fun c => τ.app (.op c)) n (iterRes S X f n z) =
      iterRes S Y f n (iterMap.{u,u,u} (fun c => τ.app (.op c)) n z) := by
  induction n generalizing a a' with
  | zero => exact congrArg (fun k : X.obj a ⟶ Y.obj a' => k z) (τ.naturality f.op)
  | succ n ih =>
    rcases z with ⟨b,g,x⟩
    let y := S.lift f g
    exact congrArg (fun v : Iter.{u,u,u} G Y.obj n y.1 =>
      (⟨y.1,y.2.1,v⟩ : Iter.{u,u,u} G Y.obj (n+1) a')) (ih y.2.2 x)

def packedPayload {Y : Family B} (τ : X.toPresheaf ⟶ Y.toPresheaf) :
    (packedFamily S X).toPresheaf ⟶ (packedFamily S Y).toPresheaf where
  app _ := TypeCat.ofHom (fun z => ⟨z.1,iterMap.{u,u,u} (fun c => τ.app (.op c)) z.1 z.2⟩)
  naturality _ _ f := by ext z; exact congrArg (Sigma.mk z.1) (iter_payload S X τ f.unop z.1 z.2)

theorem comparison_payload {Y : Family B} (τ : X.toPresheaf ⟶ Y.toPresheaf) :
    valuePayload S X τ ≫ (baseComparison S Y).hom =
      (baseComparison S X).hom ≫ packedPayload S X τ := by
  apply NatTrans.ext; funext a
  ext z
  exact extension_natural.{u,u,u} (G := G) (fun b => τ.app (.op b)) z

namespace PredicateExample
/-- A grade really chooses its successor: the subtype cut out by its predicate. -/
structure Grade (A B : Type) : Type 1 where
  pred : A → Bool
  endpoint : B = {x : A // pred x = true}

def lift {A A' B : Type} (f : A' ⟶ A) (g : Grade A B) : Lifted Grade A' B := by
  obtain ⟨p,rfl⟩ := g
  exact ⟨{x : A' // p (f x) = true}, ⟨fun x => p (f x),rfl⟩,
    TypeCat.ofHom (fun x => ⟨f x.1,x.2⟩)⟩

def split : Split Grade where
  lift := lift
  lift_id := by rintro A B ⟨p,rfl⟩; rfl
  lift_comp := by rintro A A' A'' B f k ⟨p,rfl⟩; rfl

/-- A terminal payload is a Boolean observation of the final state; restrictions act by precomposition. -/
def observations : Family (Type) where
  obj A := ULift.{1} (A → Bool)
  res f x := ⟨fun y => x.down (f y)⟩
  res_id _ := rfl
  res_comp _ _ _ := rfl

def positive : Grade Bool {x : Bool // x = true} := ⟨id,rfl⟩
def keepFalse : Unit ⟶ Bool := TypeCat.ofHom (fun _ => false)

theorem original_successor_inhabited : Nonempty {x : Bool // positive.pred x = true} :=
  ⟨⟨true,rfl⟩⟩

theorem restricted_successor_empty : IsEmpty (split.lift keepFalse positive).1 := by
  refine ⟨fun x => ?_⟩
  exact Bool.noConfusion x.2

/-- A base arrow with no section. Thus the test does not rely on invertible base change. -/
theorem test_map_has_no_section :
    ¬ ∃ s : Bool ⟶ Unit, s ≫ keepFalse = 𝟙 Bool := by
  rintro ⟨s,h⟩
  have := congrArg (fun k : Bool ⟶ Bool => k true) h
  exact Bool.noConfusion this

theorem singleton_changes_successor :
    IsEmpty (valueRes split observations keepFalse
      (⟨_,singleton positive,⟨fun _ => true⟩⟩ : Value.{1,1,1} Grade observations.obj Bool)).1 :=
  restricted_successor_empty

def acceptAll : Grade Bool {_x : Bool // true = true} := ⟨fun _ => true,rfl⟩

def observedGrade : Value.{1,1,1} Grade observations.obj Bool :=
  ⟨_, singleton acceptAll, ⟨fun x => x.1⟩⟩

/-- The terminal payload also sees the specific induced arrow, even when the successor
type is the same for both reindexings. -/
theorem two_restrictions_distinct :
    valueRes split observations keepFalse observedGrade ≠
      valueRes split observations (TypeCat.ofHom (fun _ : Unit => true)) observedGrade := by
  intro h
  have h' : (⟨fun _ : {x : Unit // true = true} => false⟩ :
      ULift.{1} ({x : Unit // true = true} → Bool)) =
      ⟨fun _ => true⟩ := by
    injection h with _ he
    injection he with _ hp
  exact Bool.noConfusion (congrArg (fun z => z.down ⟨(),rfl⟩) h')

end PredicateExample
end ContextualComposition.FiniteTelescope.Reindex
