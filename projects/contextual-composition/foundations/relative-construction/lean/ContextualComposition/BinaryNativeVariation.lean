module
public import ContextualComposition.NativeWordMap

@[expose] public section
/-! The opaque binary aggregation cell equation at a selected raw fibre. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "𝟘ₐ" => 𝟙_ C
local notation "MC" => symmetricCross (C:=C)
section Raw
variable {T : Bi (coeff (C:=C))}
variable {X U Y W : Type u} (xs : List X) (ys : List Y) (us : X → List U) (vs : Y → List W)
variable (V : X → C) (P : Y → C) (A : X → U → C) (B : Y → W → C)
local notation "Av" => fun x => T.obj (V x)
local notation "Bv" => fun y => T.obj (P y)
local notation "LA" => fun x u => T.obj (V x) (A x u)
local notation "LB" => fun y v => T.obj (P y) (B y v)
local notation "J₁" => indexInput A us
local notation "J₂" => indexInput B vs
local notation "rawA" => quadLabels (T:=T) LA LB
local notation "src" => fourOccurrenceExpr xs ys us vs
local notation "dst" => fourJointExpr xs ys us vs
local notation "circuit" => fourExchangeChart xs ys us vs

section Native
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (N : GridBinary (symmetricCross (C:=C)) R L) (NR : GatherOuterNat R) (NL : GatherLeftNat L)
variable {I : C} (m : Middle T I)
variable {a b c d : C}
variable (β : ∀ x : X, inner (S:=binary (Additive.ofBraided (C:=C)).sum) (Z:=𝟙_ C) (indexInput A us) x ⟶ b)
variable (θ : ∀ y : Y, inner (S:=binary (Additive.ofBraided (C:=C)).sum) (Z:=𝟙_ C) (indexInput B vs) y ⟶ d)
variable (α : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) V xs ⟶ a)
variable (γ : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) P ys ⟶ c)
local notation "Araw" => separateLeafLabels (T:=T) V P A B
local notation "Braw" => jointLeafLabels (T:=T) V P A B

def separateNestedCell :=
  occurrenceFirst R L Av Bv xs ys (J₁).terms (J₂).terms ≫
    T.map (dep R V (J₁) L xs β α) (dep R P (J₂) L ys θ γ)

def separateWordCell : fold 𝒮 𝟘ₐ Araw (src).leaves ⟶ T.obj (T.obj a b) (T.obj c d) :=
  compressGrid Araw src ≫ eqToHom (raw_src_eq (T:=T) xs ys us vs V P A B) ≫
    separateNestedCell xs ys us vs V P A B R L β θ α γ

def jointWordCell : fold 𝒮 𝟘ₐ Braw (dst).leaves ⟶ T.obj (T.obj a c) (T.obj b d) :=
  compressGrid Braw dst ≫
    eqToHom (raw_joint_shape xs ys us vs A B (fun x u y v => T.obj (T.obj (V x) (P y)) (T.obj u v))) ≫
    actRect (S:=𝒮) (Z:=𝟘ₐ) xs ys (jointInnerCell R L V P (J₁) (J₂) β θ) ≫
    jointOuterCell (b:=b) (d:=d) R L xs ys V P α γ

set_option backward.isDefEq.respectTransparency false in
include N NR NL in
theorem binary_word_cell_square (mi : MiddleInv m)
    (h : MedialLinear m R L) (j : MedialInner m R L) :
    AddressOrder.mapSum additiveStructure Araw (gridOrder circuit) ≫
      act 𝒮 𝟘ₐ (fun t => (binaryLeafIso V P A B m mi t).hom) (dst).leaves ≫
      jointWordCell xs ys us vs V P A B R L β θ α γ =
    separateWordCell xs ys us vs V P A B R L β θ α γ ≫ m.cell a b c d := by
  let d₀ := fun x u y v => T.obj (T.obj (V x) u) (T.obj (P y) v)
  let d₁ := fun x u y v => T.obj (T.obj (V x) (P y)) (T.obj u v)
  let leaf := fun x u y v => m.cell (V x) u (P y) v
  let hsrc := raw_src_eq (T:=T) xs ys us vs V P A B
  let hdst := raw_dst_eq (T:=T) xs ys us vs V P A B
  let hnew := raw_joint_shape xs ys us vs A B d₁
  let f := GridCircuit.eval MC Araw circuit
  let τ := exchangeInner (T:=T) MC Av Bv xs ys (J₁).terms (J₂).terms
  let p := fun t => (binaryLeafIso V P A B m mi t).hom
  let G := GridExpr.actE (S:=𝒮) (Z:=𝟘ₐ) p dst
  let F := actRect (S:=𝒮) (Z:=𝟘ₐ) xs ys (fun x y =>
      actRect (S:=𝒮) (Z:=𝟘ₐ) ((J₁).terms x) ((J₂).terms y) (fun u v => leaf x u y v))
  let k :=
    actRect (S:=𝒮) (Z:=𝟘ₐ) xs ys (jointInnerCell R L V P (J₁) (J₂) β θ) ≫
      jointOuterCell (b:=b) (d:=d) R L xs ys V P α γ
  have ep : G ≫ eqToHom hnew = eqToHom hdst ≫ F :=
    heq_paste hdst hnew (raw_joint_act xs ys us vs A B d₀ leaf)
  have ec : f ≫ eqToHom hdst = eqToHom hsrc ≫ τ :=
    heq_paste hsrc hdst (raw_exchange_heq (T:=T) xs ys us vs V P A B)
  have H :
      separateNestedCell xs ys us vs V P A B R L β θ α γ ≫ m.cell a b c d = τ ≫ (F ≫ k) := by
    unfold separateNestedCell
    rw [Category.assoc]
    exact binary_native_routes MC R L N xs ys NR NL V P (J₁) (J₂) β θ α γ m h j
  unfold separateWordCell jointWordCell
  rw [Category.assoc, Category.assoc]
  change _ ≫ act 𝒮 𝟘ₐ p (dst).leaves ≫ (compressGrid Braw dst ≫ eqToHom hnew ≫ k) =
    compressGrid Araw src ≫ eqToHom hsrc ≫ _
  rw [← Category.assoc (act 𝒮 𝟘ₐ p (dst).leaves), compressGrid_natural, Category.assoc,
    ← Category.assoc G, ep]
  simp only [Category.assoc]
  have ca := congrArg (fun d => d ≫ eqToHom hdst ≫ F ≫ k) (compressGrid_order Araw circuit)
  have cb := congrArg (fun d => compressGrid Araw src ≫ d ≫ F ≫ k) ec
  have cc := congrArg (fun d => compressGrid Araw src ≫ eqToHom hsrc ≫ d) H.symm
  simp only [Category.assoc] at ca cb
  exact ca.trans (cb.trans cc)

end Native
end Raw

section RelabelledCell
variable {Q V : Type u} (A B : Q → C) (f : V → Q)
local notation "ℱ" => fold 𝒮 𝟘ₐ

def localCellToGlobal {loc : List V} {word : List Q} (h : loc.map f = word)
    {s : C} (p : ℱ (fun x => A (f x)) loc ⟶ s) : ℱ A word ⟶ s :=
  eqToHom ((congrArg (ℱ A) h.symm).trans (std_fold_map A f loc)) ≫ p

set_option backward.isDefEq.respectTransparency false in
theorem local_cell_square {ls lt : List V} {gs gt : List Q}
    (P : AddressOrder V ls lt) (Q : AddressOrder Q gs gt)
    (hs : ls.map f = gs) (ht : lt.map f = gt) (hsn : gs.Nodup)
    (φ : ∀ z, A z ⟶ B z) {a b : C}
    (p : ℱ (fun x => A (f x)) ls ⟶ a)
    (q : ℱ (fun x => B (f x)) lt ⟶ b) (r : a ⟶ b)
    (h : AddressOrder.mapSum additiveStructure (fun x => A (f x)) P ≫
      act 𝒮 𝟘ₐ (fun x => φ (f x)) lt ≫ q = p ≫ r) :
    AddressOrder.mapSum additiveStructure A Q ≫ act 𝒮 𝟘ₐ φ gt ≫ localCellToGlobal B f ht q =
      localCellToGlobal A f hs p ≫ r := by
  subst gs
  subst gt
  have e := tagged_permutation_coherent A hsn Q (P.relabel f)
  rw [e]
  let A₀ := eqToHom (std_fold_map A f ls)
  let A₁ := eqToHom (std_fold_map A f lt)
  let B₁ := eqToHom (std_fold_map B f lt)
  have m := relabel_mapSum A f P
  have n : A₁ ≫ act 𝒮 𝟘ₐ (fun x => φ (f x)) lt =
      act 𝒮 𝟘ₐ φ (lt.map f) ≫ B₁ := std_act_map A f φ lt
  change AddressOrder.mapSum additiveStructure A (P.relabel f) ≫ act 𝒮 𝟘ₐ φ (lt.map f) ≫
    (B₁ ≫ q) = (A₀ ≫ p) ≫ r
  rw [← Category.assoc (act 𝒮 𝟘ₐ φ (lt.map f)), ← n, ← Category.assoc,
    ← reassoc_of% m]
  simp only [Category.assoc]
  exact congrArg (fun u => A₀ ≫ u) h

end RelabelledCell
end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
