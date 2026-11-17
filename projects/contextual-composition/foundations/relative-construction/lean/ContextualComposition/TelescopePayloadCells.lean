module
public import ContextualComposition.TelescopeExtension
public import Mathlib.CategoryTheory.Pi.Basic
@[expose] public section
namespace ContextualComposition.FiniteTelescope.Extension
open CategoryTheory CategoryTheory.Functor
universe u w t s
variable {B : Type u} {G : Span.{u,u} B} [∀ a b, Category.{w} (G a b)]
variable {X Y : B → Type u} [∀ b, Category.{t} (X b)] [∀ b, Category.{s} (Y b)]
variable {F H J : ∀ b, X b ⥤ Y b}

def valueCell (τ : ∀ b, F b ⟶ H b) (a : B) :
    valueFunctor (G := G) F a ⟶ valueFunctor H a where
  app z := ValueHom.mk (ChainHom.ident z.2.1) ((τ z.1).app z.2.2)
  naturality x y f := by
    change ValueHom x y at f
    cases f with
    | @mk b p q x y r h =>
      change ValueHom.mk (ChainHom.compose r (ChainHom.ident q)) ((F b).map h ≫ (τ b).app y) =
        ValueHom.mk (ChainHom.compose (ChainHom.ident p) r) ((τ b).app x ≫ (H b).map h)
      rw [ChainHom.compose_ident, ChainHom.ident_compose, (τ b).naturality]

def packedCellAt (τ : ∀ b, F b ⟶ H b) {a : B} (n : Nat) (z : Iter.{u,u,u} G X n a) :
    PackedHom (packedObj F ⟨n,z⟩) (packedObj H ⟨n,z⟩) :=
  match n with
  | 0 => .zero ((τ a).app z)
  | n+1 => .succ (𝟙 z.2.1) (packedCellAt τ n z.2.2)

theorem packedCell_naturality (τ : ∀ b, F b ⟶ H b) {a} {x y : Packed G X a} (f : PackedHom x y) :
    PackedHom.compose (packedAction F f) (packedCellAt τ y.1 y.2) =
      PackedHom.compose (packedCellAt τ x.1 x.2) (packedAction H f) := by
  induction f with
  | zero h => exact congrArg PackedHom.zero ((τ _).naturality h)
  | succ k r ih =>
    change PackedHom.succ (k ≫ 𝟙 _) _ = PackedHom.succ (𝟙 _ ≫ k) _
    rw [Category.comp_id,Category.id_comp]
    exact congrArg (PackedHom.succ k) ih

def packedCell (τ : ∀ b, F b ⟶ H b) (a : B) :
    packedFunctor (G := G) F a ⟶ packedFunctor H a where
  app z := packedCellAt τ z.1 z.2
  naturality _ _ f := packedCell_naturality τ f

theorem packedCellAt_id (F : ∀ b, X b ⥤ Y b) {a} (n : Nat) (z : Iter.{u,u,u} G X n a) :
    packedCellAt (fun b => 𝟙 (F b)) n z = PackedHom.ident (packedObj F ⟨n,z⟩) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => rcases z with ⟨b,g,p⟩; exact congrArg (PackedHom.succ (𝟙 g)) (ih p)

theorem packedCellAt_comp (τ : ∀ b, F b ⟶ H b) (σ : ∀ b, H b ⟶ J b)
    {a} (n : Nat) (z : Iter.{u,u,u} G X n a) :
    packedCellAt (fun b => τ b ≫ σ b) n z =
      PackedHom.compose (packedCellAt τ n z) (packedCellAt σ n z) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rcases z with ⟨b,g,p⟩
    change PackedHom.succ (𝟙 g) _ = PackedHom.succ ((𝟙 g) ≫ 𝟙 g) _
    rw [Category.id_comp]
    exact congrArg (PackedHom.succ (𝟙 g)) (ih p)

def valueFamilyAction (a : B) :
    (∀ b, X b ⥤ Y b) ⥤ (Value.{u,u,u} G X a ⥤ Value.{u,u,u} G Y a) where
  obj F := valueFunctor F a
  map τ := valueCell τ a
  map_id F := by apply NatTrans.ext; rfl
  map_comp τ σ := by
    apply NatTrans.ext; funext z
    change ValueHom.mk (ChainHom.ident z.2.1) _ =
      ValueHom.mk (ChainHom.compose (ChainHom.ident z.2.1) (ChainHom.ident z.2.1)) _
    rw [ChainHom.ident_compose]
    rfl

def packedFamilyAction (a : B) :
    (∀ b, X b ⥤ Y b) ⥤ (Packed G X a ⥤ Packed G Y a) where
  obj F := packedFunctor F a
  map τ := packedCell τ a
  map_id F := by apply NatTrans.ext; funext z; exact packedCellAt_id F z.1 z.2
  map_comp τ σ := by apply NatTrans.ext; funext z; exact packedCellAt_comp τ σ z.1 z.2

private theorem packedPrefixHEq {a b} {g : G a b} {x y x' y' : Packed G Y b}
    {r : PackedHom x y} {s : PackedHom x' y'} (hx : x = x') (hy : y = y') (hr : HEq r s) :
    HEq (prefixPackedHom (𝟙 g) r) (prefixPackedHom (𝟙 g) s) := by
  subst x'; subst y'; cases hr; rfl

theorem encode_cell (τ : ∀ b, F b ⟶ H b) {a b} (p : Chain G a b) (x : X b) :
    HEq (encodeChain (ChainHom.ident p) ((τ b).app x))
      (packedCellAt τ (pack.{u,u,u} p x).1 (pack.{u,u,u} p x).2) := by
  induction p with
  | nil => rfl
  | @cons i j b g p ih =>
    exact packedPrefixHEq (g := g)
      (extension_natural.{u,u,u} (G := G) (fun b => (F b).obj) ⟨b,p,x⟩)
      (extension_natural.{u,u,u} (G := G) (fun b => (H b).obj) ⟨b,p,x⟩) (ih x)

private theorem natTransHEq {C D : Type*} [Category* C] [Category* D]
    {P Q P' Q' : C ⥤ D} (α : P ⟶ Q) (β : P' ⟶ Q')
    (hp : P = P') (hq : Q = Q') (h : ∀ x, HEq (α.app x) (β.app x)) : HEq α β := by
  subst P'; subst Q'
  apply heq_of_eq
  apply NatTrans.ext
  funext x
  exact eq_of_heq (h x)

/-- Equality of functors from the category of payload changes, including its arbitrary 2-cells. -/
theorem forward_family (a : B) :
    valueFamilyAction (G := G) (X := X) (Y := Y) a ⋙
      (whiskeringRight _ _ _).obj (forward a) =
    packedFamilyAction (G := G) (X := X) (Y := Y) a ⋙
      (whiskeringLeft _ _ _).obj (forward a) := by
  apply Functor.hext
  · intro F; exact forward_payload F a
  · intro F H τ
    apply natTransHEq _ _ (forward_payload F a) (forward_payload H a)
    intro z
    exact encode_cell τ z.2.1 z.2.2

private theorem valuePrefixHEq {a b} {g : G a b} {x y x' y' : Value.{u,u,u} G Y b}
    {r : ValueHom x y} {s : ValueHom x' y'} (hx : x = x') (hy : y = y') (hr : HEq r s) :
    HEq (prefixHom (𝟙 g) r) (prefixHom (𝟙 g) s) := by subst x'; subst y'; cases hr; rfl

private theorem unpack_obj_payload (F : ∀ b, X b ⥤ Y b) {a} (z : Packed G X a) :
    (backward a).obj (packedObj F z) = (valueFunctor F a).obj ((backward a).obj z) :=
  Functor.congr_obj (backward_payload F a) z

theorem decode_cell (τ : ∀ b, F b ⟶ H b) {a} (n : Nat) (z : Iter.{u,u,u} G X n a) :
    HEq (decode (packedCellAt τ n z)) ((valueCell (G := G) τ a).app (unpack.{u,u,u} n z)) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rcases z with ⟨b,g,p⟩
    exact valuePrefixHEq (g := g) (unpack_obj_payload F ⟨n,p⟩)
      (unpack_obj_payload H ⟨n,p⟩) (ih p)

theorem backward_family (a : B) :
    packedFamilyAction (G := G) (X := X) (Y := Y) a ⋙
      (whiskeringRight _ _ _).obj (backward a) =
    valueFamilyAction (G := G) (X := X) (Y := Y) a ⋙
      (whiskeringLeft _ _ _).obj (backward a) := by
  apply Functor.hext
  · intro F; exact backward_payload F a
  · intro F H τ
    apply natTransHEq _ _ (backward_payload F a) (backward_payload H a)
    intro z
    exact decode_cell τ z.1 z.2

theorem packedCell_zero (τ : ∀ b, F b ⟶ H b) (a : B) (x : X a) :
    (packedCell (G := G) τ a).app ⟨0,x⟩ = PackedHom.zero ((τ a).app x) := rfl

/-- Faithfulness is joint over starting states; a single state need not reach every other state. -/
theorem packedCell_joint_faithful (τ σ : ∀ b, F b ⟶ H b)
    (h : ∀ a, packedCell (G := G) τ a = packedCell σ a) : τ = σ := by
  funext a
  apply NatTrans.ext
  funext x
  apply (zeroHomEquiv (G := G) ((F a).obj x) ((H a).obj x)).injective
  exact NatTrans.congr_app (h a) ⟨0,x⟩

theorem valueCell_joint_faithful (τ σ : ∀ b, F b ⟶ H b)
    (h : ∀ a, valueCell (G := G) τ a = valueCell σ a) : τ = σ := by
  funext a
  apply NatTrans.ext
  funext x
  apply (zeroHomEquiv (G := G) ((F a).obj x) ((H a).obj x)).injective
  exact congrArg (fun f => (forward a).map f) (NatTrans.congr_app (h a) (emptyValue x))

/-- The explicit zero-length inclusion does not turn a one-way payload map into a reversible one. -/
theorem no_reverse_at_zero (τ : ∀ b, F b ⟶ H b) {a : B} (x : X a)
    (h : IsEmpty ((H a).obj x ⟶ (F a).obj x)) :
    ¬ IsIso ((packedCell (G := G) τ a).app ⟨0,x⟩) := by
  intro i
  obtain ⟨r,_,_⟩ := i.out
  exact h.false ((zeroHomEquiv (G := G) ((H a).obj x) ((F a).obj x)).symm r)


/-- Exact observation boundary for one starting fibre. Only payloads at the endpoints
of actual chains are tested; the witness chain is not replaced by an arbitrary state. -/
theorem valueCell_eq_iff_reachable (τ σ : ∀ b, F b ⟶ H b) (a : B) :
    valueCell (G := G) τ a = valueCell σ a ↔
      ∀ (b : B) (_ : Chain G a b) (x : X b), (τ b).app x = (σ b).app x := by
  constructor
  · intro h b p x
    have h' := NatTrans.congr_app h (⟨b,p,x⟩ : Value.{u,u,u} G X a)
    change ValueHom.mk (ChainHom.ident p) ((τ b).app x) =
      ValueHom.mk (ChainHom.ident p) ((σ b).app x) at h'
    injection h' with _ _ _ _ _ _ hk
  · intro h
    apply NatTrans.ext; funext z
    exact congrArg (ValueHom.mk (ChainHom.ident z.2.1)) (h z.1 z.2.1 z.2.2)

theorem packedCell_eq_iff_valueCell (τ σ : ∀ b, F b ⟶ H b) (a : B) :
    packedCell (G := G) τ a = packedCell σ a ↔ valueCell (G := G) τ a = valueCell σ a := by
  constructor
  · intro h
    apply NatTrans.ext; funext z
    apply (categoryEquivalence (G := G) (X := Y) a).functor.map_injective
    apply eq_of_heq
    exact (encode_cell τ z.2.1 z.2.2).trans
      ((heq_of_eq (NatTrans.congr_app h (pack z.2.1 z.2.2))).trans (encode_cell σ z.2.1 z.2.2).symm)
  · intro h
    apply NatTrans.ext; funext z
    apply (categoryEquivalence (G := G) (X := Y) a).inverse.map_injective
    apply eq_of_heq
    exact (decode_cell τ z.1 z.2).trans
      ((heq_of_eq (NatTrans.congr_app h (unpack z.1 z.2))).trans (decode_cell σ z.1 z.2).symm)
end ContextualComposition.FiniteTelescope.Extension
