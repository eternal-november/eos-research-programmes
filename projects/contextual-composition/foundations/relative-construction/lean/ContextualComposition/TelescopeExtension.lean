module
public import ContextualComposition.TelescopeMorphisms
public import Mathlib.CategoryTheory.Equivalence
@[expose] public section
namespace ContextualComposition.FiniteTelescope
open CategoryTheory
universe u w t
variable {B : Type u} {G : Span.{u,u} B} [∀ a b, Category.{w} (G a b)]
variable {X : B → Type u} [∀ b, Category.{t} (X b)]

/-- On the extension side, a single shared terminal state indexes the two independent arrows. -/
inductive ValueHom {a : B} : Value.{u,u,u} G X a → Value.{u,u,u} G X a → Type (max u w t)
  | mk {b : B} {p q : Chain G a b} {x y : X b}
      (f : ChainHom p q) (h : x ⟶ y) : ValueHom ⟨b,p,x⟩ ⟨b,q,y⟩

namespace ValueHom
def ident {a} (z : Value.{u,u,u} G X a) : ValueHom z z := .mk (ChainHom.ident _) (𝟙 _)
def compose {a} {x y z : Value.{u,u,u} G X a} (f : ValueHom x y) (g : ValueHom y z) : ValueHom x z :=
  match x,y,z,f,g with
  | _,_,_,.mk p h,.mk q k => .mk (ChainHom.compose p q) (h ≫ k)
instance valueCategory (a : B) : Category (Value.{u,u,u} G X a) where
  Hom := ValueHom
  id := ident
  comp := compose
  id_comp f := by cases f; simp [ident,compose,ChainHom.ident_compose]
  comp_id f := by cases f; simp [ident,compose,ChainHom.compose_ident]
  assoc f g h := by cases f; cases g; cases h; simp [compose,ChainHom.compose_assoc,Category.assoc]
end ValueHom

abbrev Packed (G : Span.{u,u} B) (X : B → Type u) (a : B) := Σ n, Iter.{u,u,u} G X n a

/-- The independent coproduct of iterates: at zero a payload arrow; at successor a grade
arrow and a tail arrow in the previous iterate. No comparison functor occurs in its definition. -/
inductive PackedHom : {a : B} → Packed G X a → Packed G X a → Type (max u w t)
  | zero {a} {x y : X a} (h : x ⟶ y) : PackedHom (a := a) ⟨0,x⟩ ⟨0,y⟩
  | succ {a b n m} {g j : G a b} {p : Iter.{u,u,u} G X n b} {q : Iter.{u,u,u} G X m b} (f : g ⟶ j)
      (r : PackedHom (a := b) ⟨n,p⟩ ⟨m,q⟩) :
      PackedHom (a := a) ⟨n+1,b,g,p⟩ ⟨m+1,b,j,q⟩
namespace PackedHom
def identAt {a : B} (n : Nat) (x : Iter.{u,u,u} G X n a) : PackedHom (a := a) ⟨n,x⟩ ⟨n,x⟩ :=
  match n with
  | 0 => .zero (𝟙 (show X a from x))
  | n+1 => .succ (𝟙 x.2.1) (identAt n x.2.2)
def ident {a} (z : Packed G X a) : PackedHom z z := identAt z.1 z.2

def compose {a} {x y z : Packed G X a} (f : PackedHom x y) (g : PackedHom y z) : PackedHom x z :=
  match a,x,y,z,f,g with
  | _,_,_,_,.zero h,.zero k => .zero (h ≫ k)
  | _,_,_,_,.succ h r,.succ k s => .succ (h ≫ k) (compose r s)
instance packedCategory (a : B) : Category (Packed G X a) where
  Hom := PackedHom
  id := ident
  comp := compose
  id_comp f := by
    induction f with
    | zero => simp [ident,identAt,compose]
    | succ h r ih =>
      change PackedHom.succ _ _ = _
      congr 1
      · simp
  comp_id f := by
    induction f with
    | zero => simp [ident,identAt,compose]
    | succ h r ih =>
      change PackedHom.succ _ _ = _
      congr 1
      · simp
  assoc f g h := by
    induction f with
    | zero => cases g; cases h; simp [compose, Category.assoc]
    | succ f r ih => cases g with
      | succ g s => cases h with
        | succ h t => simp [compose, Category.assoc, ih]
end PackedHom

namespace Extension
def encodeChain {a b} {p q : Chain G a b} (f : ChainHom p q) {x y : X b} (h : x ⟶ y) :
    PackedHom (pack.{u,u,u} p x) (pack.{u,u,u} q y) :=
  match a,b,p,q,f with
  | _,_,_,_,.nil _ => .zero h
  | _,_,_,_,.cons k r => .succ k (encodeChain r h)

def encode {a} {x y : Value.{u,u,u} G X a} (f : ValueHom x y) :
    PackedHom (extensionEquiv.{u,u,u} G X a x) (extensionEquiv.{u,u,u} G X a y) :=
  match f with
  | .mk p h => encodeChain p h

theorem encodeChain_id {a b} (p : Chain G a b) (x : X b) :
    encodeChain (ChainHom.ident p) (𝟙 x) = PackedHom.ident (pack.{u,u,u} p x) := by
  induction p with
  | nil => rfl
  | cons g p ih => exact congrArg (PackedHom.succ (𝟙 g)) (ih x)

theorem encodeChain_comp {a b} {p q r : Chain G a b} (f : ChainHom p q) (g : ChainHom q r)
    {x y z : X b} (h : x ⟶ y) (k : y ⟶ z) :
    encodeChain (ChainHom.compose f g) (h ≫ k) = PackedHom.compose (encodeChain f h) (encodeChain g k) := by
  induction f with
  | nil => cases g; rfl
  | cons f r ih => cases g with
    | cons g s => exact congrArg (PackedHom.succ (f ≫ g)) (ih s h k)

def forward (a : B) : Value.{u,u,u} G X a ⥤ Packed G X a where
  obj := extensionEquiv.{u,u,u} G X a
  map := encode
  map_id z := encodeChain_id z.2.1 z.2.2
  map_comp f g := by cases f; cases g; apply encodeChain_comp

def prefixValue {a b} (g : G a b) (z : Value.{u,u,u} G X b) : Value.{u,u,u} G X a :=
  ⟨z.1,.cons g z.2.1,z.2.2⟩

def prefixHom {a b} {g j : G a b} (k : g ⟶ j) {x y : Value.{u,u,u} G X b}
    (r : ValueHom x y) : ValueHom (prefixValue g x) (prefixValue j y) :=
  match r with
  | .mk p h => .mk (.cons k p) h

def decode {a} {x y : Packed G X a} (f : PackedHom x y) :
    ValueHom (unpack.{u,u,u} x.1 x.2) (unpack.{u,u,u} y.1 y.2) :=
  match f with
  | .zero h => .mk (.nil _) h
  | .succ k r => prefixHom k (decode r)

theorem decode_id {a} (n : Nat) (x : Iter.{u,u,u} G X n a) :
    decode (PackedHom.identAt n x) = ValueHom.ident (unpack.{u,u,u} n x) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rcases x with ⟨b,g,p⟩
    change prefixHom (𝟙 g) (decode (PackedHom.identAt n p)) = _
    rw [ih]
    rfl

theorem prefix_comp {a b} {g j l : G a b} (k : g ⟶ j) (m : j ⟶ l)
    {x y z : Value.{u,u,u} G X b} (r : ValueHom x y) (s : ValueHom y z) :
    prefixHom (k ≫ m) (ValueHom.compose r s) = ValueHom.compose (prefixHom k r) (prefixHom m s) := by
  cases r; cases s; rfl

theorem decode_comp {a} {x y z : Packed G X a} (f : PackedHom x y) (g : PackedHom y z) :
    decode (PackedHom.compose f g) = ValueHom.compose (decode f) (decode g) := by
  induction f with
  | zero => cases g; rfl
  | succ k r ih => cases g with
    | succ m s =>
      change prefixHom (k ≫ m) (decode (PackedHom.compose r s)) = _
      rw [ih, prefix_comp]
      rfl

def backward (a : B) : Packed G X a ⥤ Value.{u,u,u} G X a where
  obj x := unpack.{u,u,u} x.1 x.2
  map := decode
  map_id z := decode_id z.1 z.2
  map_comp := decode_comp

private theorem prefix_heq {a b} {g j : G a b} (k : g ⟶ j) {x y x' y' : Value.{u,u,u} G X b}
    {r : ValueHom x y} {s : ValueHom x' y'} (hx : x = x') (hy : y = y') (hr : HEq r s) :
    HEq (prefixHom k r) (prefixHom k s) := by subst x'; subst y'; cases hr; rfl

theorem decode_encode_chain {a b} {p q : Chain G a b} (f : ChainHom p q) {x y : X b} (h : x ⟶ y) :
    HEq (decode (encodeChain f h)) (ValueHom.mk f h) := by
  induction f with
  | nil => rfl
  | cons k r ih =>
    exact prefix_heq k (unpack_pack _ _) (unpack_pack _ _) (ih h)

def prefixPacked {a b} (g : G a b) (z : Packed G X b) : Packed G X a :=
  ⟨z.1+1,b,g,z.2⟩

def prefixPackedHom {a b} {g j : G a b} (k : g ⟶ j) {x y : Packed G X b}
    (r : PackedHom x y) : PackedHom (prefixPacked g x) (prefixPacked j y) := .succ k r

private theorem prefixPacked_heq {a b} {g j : G a b} (k : g ⟶ j) {x y x' y' : Packed G X b}
    {r : PackedHom x y} {s : PackedHom x' y'} (hx : x = x') (hy : y = y') (hr : HEq r s) :
    HEq (prefixPackedHom k r) (prefixPackedHom k s) := by subst x'; subst y'; cases hr; rfl

theorem encode_prefix {a b} {g j : G a b} (k : g ⟶ j) {x y : Value.{u,u,u} G X b}
    (r : ValueHom x y) : encode (prefixHom k r) = prefixPackedHom k (encode r) := by
  cases r; rfl

theorem encode_decode {a} {x y : Packed G X a} (f : PackedHom x y) :
    HEq (encode (decode f)) f := by
  induction f with
  | zero => rfl
  | succ k r ih =>
    change HEq (encode (prefixHom k (decode r))) _
    rw [encode_prefix]
    exact prefixPacked_heq k (pack_unpack _ _) (pack_unpack _ _) ih

theorem forward_backward (a : B) :
    forward (G := G) (X := X) a ⋙ backward a = 𝟭 _ := by
  apply Functor.hext
  · intro z; exact unpack_pack z.2.1 z.2.2
  · intro x y f
    change ValueHom x y at f
    cases f with
    | mk r h => exact decode_encode_chain r h

theorem backward_forward (a : B) :
    backward (G := G) (X := X) a ⋙ forward a = 𝟭 _ := by
  apply Functor.hext
  · intro z; exact pack_unpack z.1 z.2
  · intro x y f; exact encode_decode f

/-- The actual prior object equivalence, now on categories and arbitrary native arrows. -/
def categoryEquivalence (a : B) : Value.{u,u,u} G X a ≌ Packed G X a :=
  CategoryTheory.Equivalence.mk (forward a) (backward a)
    (eqToIso (forward_backward a).symm) (eqToIso (backward_forward a))

theorem no_cross_length {a} {x y : Packed G X a} (f : PackedHom x y) : x.1 = y.1 := by
  induction f with
  | zero => rfl
  | succ _ _ ih => exact congrArg Nat.succ ih

section Payload
universe t'
variable {Y : B → Type u} [∀ b, Category.{t'} (Y b)] (F : ∀ b, X b ⥤ Y b)

def valueAction {a} {x y : Value.{u,u,u} G X a} (f : ValueHom x y) :
    ValueHom (valueMap.{u,u,u} (fun b => (F b).obj) x)
      (valueMap.{u,u,u} (fun b => (F b).obj) y) :=
  match f with
  | .mk p h => .mk p ((F _).map h)

def valueFunctor (a : B) : Value.{u,u,u} G X a ⥤ Value.{u,u,u} G Y a where
  obj := valueMap.{u,u,u} (fun b => (F b).obj)
  map := valueAction F
  map_id z := by
    change ValueHom.mk _ ((F z.1).map (𝟙 _)) = _
    rw [Functor.map_id]; rfl
  map_comp f g := by
    cases f with | mk p h =>
      cases g with | mk q k =>
        change ValueHom.mk _ ((F _).map (h ≫ k)) = _
        rw [Functor.map_comp]; rfl

def packedObj {a} (z : Packed G X a) : Packed G Y a :=
  ⟨z.1,iterMap.{u,u,u} (fun b => (F b).obj) z.1 z.2⟩

def packedAction {a} {x y : Packed G X a} (f : PackedHom x y) :
    PackedHom (packedObj F x) (packedObj F y) :=
  match f with
  | .zero h => .zero ((F _).map h)
  | .succ k r => .succ k (packedAction r)

theorem packedAction_id {a} (n : Nat) (x : Iter.{u,u,u} G X n a) :
    packedAction F (PackedHom.identAt n x) =
      PackedHom.ident (packedObj F ⟨n,x⟩) := by
  induction n generalizing a with
  | zero =>
    exact congrArg PackedHom.zero ((F a).map_id (show X a from x))
  | succ n ih =>
    rcases x with ⟨b,g,p⟩
    exact congrArg (PackedHom.succ (𝟙 g)) (ih p)

theorem packedAction_comp {a} {x y z : Packed G X a} (f : PackedHom x y) (g : PackedHom y z) :
    packedAction F (PackedHom.compose f g) = PackedHom.compose (packedAction F f) (packedAction F g) := by
  induction f with
  | zero h => cases g with
    | zero k =>
      change PackedHom.zero ((F _).map (h ≫ k)) = _
      rw [Functor.map_comp]; rfl
  | succ k r ih => cases g with
    | succ m s => exact congrArg (PackedHom.succ (k ≫ m)) (ih s)

def packedFunctor (a : B) : Packed G X a ⥤ Packed G Y a where
  obj := packedObj F
  map := packedAction F
  map_id z := packedAction_id F z.1 z.2
  map_comp := packedAction_comp F

theorem encode_payload {a b} {p q : Chain G a b} (f : ChainHom p q) {x y : X b} (h : x ⟶ y) :
    HEq (encodeChain f ((F b).map h)) (packedAction F (encodeChain f h)) := by
  induction f with
  | nil => rfl
  | @cons i j b g l p q k r ih =>
    exact prefixPacked_heq k (extension_natural.{u,u,u} (G := G) (fun b => (F b).obj) ⟨b,p,x⟩)
      (extension_natural.{u,u,u} (G := G) (fun b => (F b).obj) ⟨b,q,y⟩) (ih h)

theorem forward_payload (a : B) :
    valueFunctor (G := G) F a ⋙ forward a = forward a ⋙ packedFunctor F a := by
  apply Functor.hext
  · intro z; exact extension_natural (fun b => (F b).obj) z
  · intro x y f
    change ValueHom x y at f
    cases f with | mk r h => exact encode_payload F r h

theorem backward_payload (a : B) :
    packedFunctor (G := G) F a ⋙ backward a = backward a ⋙ valueFunctor F a := by
  let P := packedFunctor (G := G) F a
  let V := valueFunctor (G := G) F a
  let A := forward (G := G) (X := X) a
  let I := backward (G := G) (X := X) a
  let J := backward (G := G) (X := Y) a
  let C := forward (G := G) (X := Y) a
  have hx : I ⋙ A = 𝟭 _ := backward_forward a
  have hy : C ⋙ J = 𝟭 _ := forward_backward a
  have hn : V ⋙ C = A ⋙ P := forward_payload F a
  calc
    P ⋙ J = ((I ⋙ A) ⋙ P) ⋙ J := by rw [hx]; rfl
    _ = (I ⋙ (A ⋙ P)) ⋙ J := rfl
    _ = (I ⋙ (V ⋙ C)) ⋙ J := by rw [hn]
    _ = (I ⋙ V) ⋙ (C ⋙ J) := rfl
    _ = I ⋙ V := by rw [hy]; rfl
end Payload

theorem encode_empty {a : B} {x y : X a} (h : x ⟶ y) :
    encodeChain (G := G) (.nil a) h = PackedHom.zero h := rfl

/-- One grade arrow and one payload arrow survive independently; neither need be invertible. -/
theorem encode_singleton {a b : B} {g j : G a b} (k : g ⟶ j) {x y : X b} (h : x ⟶ y) :
    encodeChain (ChainHom.singletonArrow k) h = PackedHom.succ k (PackedHom.zero h) := rfl

/-- At zero, iterated-extension morphisms are exactly the original payload morphisms. -/
def zeroHomEquiv {a} (x y : X a) :
    (x ⟶ y) ≃ PackedHom (G := G) (X := X) (a := a) ⟨0,x⟩ ⟨0,y⟩ where
  toFun := PackedHom.zero
  invFun f := match f with | .zero h => h
  left_inv _ := rfl
  right_inv f := by cases f; rfl

/-- For a common next state the successor hom is the product, not a proposition
asserting compatibility; the tail object need not be at length zero. -/
def succHomEquiv {a b} {n m} {p : Iter.{u,u,u} G X n b} {q : Iter.{u,u,u} G X m b}
    (g j : G a b) :
    ((g ⟶ j) × PackedHom (G := G) (X := X) (a := b) ⟨n,p⟩ ⟨m,q⟩) ≃
      PackedHom (G := G) (X := X) (a := a) ⟨n+1,b,g,p⟩ ⟨m+1,b,j,q⟩ where
  toFun z := .succ z.1 z.2
  invFun f := match f with | .succ k r => ⟨k,r⟩
  left_inv _ := rfl
  right_inv f := by cases f; rfl

theorem next_state_eq {a b c} {n m} {p : Iter.{u,u,u} G X n b} {q : Iter.{u,u,u} G X m c}
    {g : G a b} {j : G a c}
    (f : PackedHom (G := G) (X := X) (a := a) ⟨n+1,b,g,p⟩ ⟨m+1,c,j,q⟩) : b = c := by
  cases f; rfl
end Extension
end ContextualComposition.FiniteTelescope
