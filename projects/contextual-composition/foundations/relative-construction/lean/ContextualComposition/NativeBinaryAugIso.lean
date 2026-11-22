module
public import ContextualComposition.NativeWordPresentation

@[expose] public section
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v w
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "𝟘ₐ" => 𝟙_ C
local notation "MC" => symmetricCross (C:=C)
variable {X Y : Type w}

theorem act_heq {A B D F : X → C} (hA : A = D) (hB : B = F)
    {p : ∀ x, A x ⟶ B x} {q : ∀ x, D x ⟶ F x} (h : ∀ x, HEq (p x) (q x))
    (xs : List X) : HEq (act 𝒮 𝟘ₐ p xs) (act 𝒮 𝟘ₐ q xs) := by
  subst D
  subst F
  have eq : p = q := funext fun x => eq_of_heq (h x)
  subst q
  rfl

theorem transpose_map (f : X → Y) {V : Type w} (ys : List V) (A : Y → V → C) (xs : List X) :
    HEq (transposeBlock MC (fun x y => A (f x) y) ys xs) (transposeBlock MC A ys (xs.map f)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    let P := fun x => fold 𝒮 𝟘ₐ (A x) ys
    let Q := fun y => fold 𝒮 𝟘ₐ (fun x => A (f x) y) xs
    let Q' := fun y => fold 𝒮 𝟘ₐ (fun x => A x y) (xs.map f)
    have h₁ : fold 𝒮 𝟘ₐ (fun t => P (f t)) xs = fold 𝒮 𝟘ₐ P (xs.map f) :=
      (std_fold_map P f xs).symm
    have h₂ : Q = Q' := funext fun y => (std_fold_map (fun x => A x y) f xs).symm
    have h₃ : HEq (zipBlock MC (A (f x)) Q ys) (zipBlock MC (A (f x)) Q' ys) := by
      rw [h₂]
    simp only [transposeBlock]
    refine structural_seq_heq ?_ ?_ ?_ ?_ h₃
    · exact congrArg (fun s => P (f x) ⊗ s) h₁
    · exact congrArg (fun G => P (f x) ⊗ fold 𝒮 𝟘ₐ G ys) h₂
    · exact congrArg (fun G => fold 𝒮 𝟘ₐ (fun y => A (f x) y ⊗ G y) ys) h₂
    · exact structural_map_heq (S:=𝒮) (a:=P (f x)) (b:=P (f x)) rfl rfl h₁ (congrArg (fun G => fold 𝒮 𝟘ₐ G ys) h₂)
        (HEq.rfl : HEq (𝟙 (P (f x))) (𝟙 (P (f x)))) ih

section Grid
variable {I : Type u} (A : I → C)
def compressGrid : (t : GridExpr I) → fold 𝒮 𝟘ₐ A t.leaves ⟶ GridExpr.eval (S:=𝒮) (Z:=𝟘ₐ) A t
  | .zero => 𝟙 _
  | .leaf x => (ρ_ (A x)).hom
  | .bin l r => join additiveStructure A l.leaves r.leaves ≫ (compressGrid l ⊗ₘ compressGrid r)

set_option backward.isDefEq.respectTransparency false in
theorem compressGrid_tail (t : GridExpr I) :
    compressGrid A t = toTail A t.leaves ≫ compressTree A t := by
  induction t with
  | zero =>
    change 𝟙 𝟘ₐ = 𝟙 𝟘ₐ ≫ 𝟙 𝟘ₐ
    rw [Category.id_comp]
  | leaf x =>
    change (ρ_ (A x)).hom = 𝟙 (A x ⊗ 𝟘ₐ) ≫ (ρ_ (A x)).hom
    rw [Category.id_comp]
  | bin l r ihL ihR =>
    let a := l.leaves
    let b := r.leaves
    let J : fold 𝒮 𝟘ₐ A (a ++ b) ⟶ fold 𝒮 𝟘ₐ A a ⊗ fold 𝒮 𝟘ₐ A b := join additiveStructure A a b
    calc
      _ = toTail A (a ++ b) ≫ (tailJoin A a b ≫ (compressTree A l ⊗ₘ compressTree A r)) := by
        change J ≫ (compressGrid A l ⊗ₘ compressGrid A r) = _
        rw [← Category.assoc, tailJoin_bridge, Category.assoc, tensorHom_comp_tensorHom, ihL, ihR]
      _ = _ := by
        have h : tailJoin A a b ≫ (compressTree A l ⊗ₘ compressTree A r) =
            eqToHom (nestedFlat A l r 𝟘ₐ) ≫ splitTail (word A l) (taggedTail A b 𝟘ₐ) ≫
              (compressTree A l ⊗ₘ compressTree A r) := by
          unfold tailJoin
          rw [Category.assoc]
        exact congrArg (fun p => toTail A (a ++ b) ≫ p) h

set_option backward.isDefEq.respectTransparency false in
theorem compressGrid_natural {A B : I → C} (p : ∀ x, A x ⟶ B x) (t : GridExpr I) :
    act 𝒮 𝟘ₐ p t.leaves ≫ compressGrid B t =
      compressGrid A t ≫ GridExpr.actE (S:=𝒮) (Z:=𝟘ₐ) p t := by
  induction t with
  | zero => rfl
  | leaf x =>
    change (p x ⊗ₘ 𝟙 𝟘ₐ) ≫ (ρ_ (B x)).hom = (ρ_ (A x)).hom ≫ p x
    rw [tensorHom_id, rightUnitor_naturality]
  | bin l r ihL ihR =>
    have e : act 𝒮 𝟘ₐ p (l.leaves ++ r.leaves) ≫ join additiveStructure B l.leaves r.leaves =
      join additiveStructure A l.leaves r.leaves ≫
        (act 𝒮 𝟘ₐ p l.leaves ⊗ₘ act 𝒮 𝟘ₐ p r.leaves) := act_append additiveNaturality p _ _
    change act 𝒮 𝟘ₐ p (l.leaves ++ r.leaves) ≫
        (_ ≫ (compressGrid B l ⊗ₘ compressGrid B r)) =
      (_ ≫ (compressGrid A l ⊗ₘ compressGrid A r)) ≫
        (GridExpr.actE (S:=𝒮) (Z:=𝟘ₐ) p l ⊗ₘ GridExpr.actE (S:=𝒮) (Z:=𝟘ₐ) p r)
    rw [← Category.assoc, e, Category.assoc, Category.assoc, tensorHom_comp_tensorHom,
      tensorHom_comp_tensorHom, ihL, ihR]

set_option backward.isDefEq.respectTransparency false in
theorem compressGrid_order {e f : GridExpr I} (p : GridCircuit I e f) :
    AddressOrder.mapSum additiveStructure A (gridOrder p) ≫ compressGrid A f =
      compressGrid A e ≫ GridCircuit.eval MC A p := by
  rw [compressGrid_tail, compressGrid_tail, ← Category.assoc, taggedTailMap_bridge, Category.assoc,
    gridOrder_semantics, independent_std_charts, Category.assoc]
end Grid

omit [MonoidalCategory C] [SymmetricCategory C] in
theorem heq_paste {a a' b b' : C} (e : a = a') (f : b = b')
    {p : a ⟶ b} {q : a' ⟶ b'} (h : HEq p q) :
    p ≫ eqToHom f = eqToHom e ≫ q := by
  subst a'
  subst b'
  have e := eq_of_heq h
  subst q
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

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

theorem rawRow_eval (x : X) :
    raggedCell (S:=𝒮) (Z:=𝟘ₐ) (T:=T) (LA x) vs LB =
      fun u y => raggedCell (S:=𝒮) (Z:=𝟘ₐ) (T:=T) (Av x) (J₂).terms Bv (A x u) y := by
  funext u y
  exact (std_fold_map (fun c => T.obj (T.obj (V x) (A x u)) (T.obj (P y) c)) (B y) (vs y)).symm

theorem raw_row_source (x : X) :
    fold 𝒮 𝟘ₐ
        (fun u => fold 𝒮 𝟘ₐ (raggedCell (S:=𝒮) (Z:=𝟘ₐ) (T:=T) (LA x) vs LB u) ys) (us x) =
    fold 𝒮 𝟘ₐ
        (fun a => fold 𝒮 𝟘ₐ (raggedCell (S:=𝒮) (Z:=𝟘ₐ) (T:=T) (Av x) (J₂).terms Bv a) ys) ((J₁).terms x) := by
  simp only [rawRow_eval (T:=T) vs V P A B x]
  exact (std_fold_map (fun a : C => fold 𝒮 𝟘ₐ
    (raggedCell (S:=𝒮) (Z:=𝟘ₐ) (T:=T) (Av x) (J₂).terms Bv a) ys) (A x) (us x)).symm

theorem raw_row_target (x : X) :
    fold 𝒮 𝟘ₐ (fun y => fold 𝒮 𝟘ₐ
      (fun u => raggedCell (S:=𝒮) (Z:=𝟘ₐ) (T:=T) (LA x) vs LB u y) (us x)) ys =
    fold 𝒮 𝟘ₐ (fun y => fold 𝒮 𝟘ₐ
      (fun a => raggedCell (S:=𝒮) (Z:=𝟘ₐ) (T:=T) (Av x) (J₂).terms Bv a y) ((J₁).terms x)) ys := by
  simp only [rawRow_eval (T:=T) vs V P A B x]
  exact congrArg (fun G => fold 𝒮 𝟘ₐ G ys) (funext fun y =>
    (std_fold_map (fun a : C => raggedCell (S:=𝒮) (Z:=𝟘ₐ) (T:=T)
      (Av x) (J₂).terms Bv a y) (A x) (us x)).symm)

theorem raw_src_eq :
    GridExpr.eval (S:=𝒮) (Z:=𝟘ₐ) rawA src =
      fold 𝒮 𝟘ₐ (fun x => fold 𝒮 𝟘ₐ
        (fun a => fold 𝒮 𝟘ₐ (raggedCell (S:=𝒮) (Z:=𝟘ₐ) (T:=T) (Av x) (J₂).terms Bv a) ys)
          ((J₁).terms x)) xs :=
  (occurrence_expr_obj (S:=𝒮) (Z:=𝟘ₐ) (T:=T) LA LB xs ys us vs).trans
    (congrArg (fun G => fold 𝒮 𝟘ₐ G xs) (funext (raw_row_source (T:=T) ys us vs V P A B)))

theorem raw_dst_eq :
    GridExpr.eval (S:=𝒮) (Z:=𝟘ₐ) rawA dst =
      fold 𝒮 𝟘ₐ (fun x => fold 𝒮 𝟘ₐ (fun y => fold 𝒮 𝟘ₐ
        (fun a => raggedCell (S:=𝒮) (Z:=𝟘ₐ) (T:=T) (Av x) (J₂).terms Bv a y) ((J₁).terms x)) ys) xs :=
  (joint_expr_obj (S:=𝒮) (Z:=𝟘ₐ) (T:=T) LA LB xs ys us vs).trans
    (congrArg (fun G => fold 𝒮 𝟘ₐ G xs) (funext (raw_row_target (T:=T) ys us vs V P A B)))

theorem raw_exchange_heq :
    HEq (GridCircuit.eval MC rawA circuit)
      (exchangeInner (T:=T) MC Av Bv xs ys (J₁).terms (J₂).terms) := by
  apply (fourExchangeChart_eval MC (T:=T) LA LB xs ys us vs).trans
  unfold exchangeInner
  apply act_heq (funext (raw_row_source (T:=T) ys us vs V P A B))
    (funext (raw_row_target (T:=T) ys us vs V P A B))
  intro x
  have h (D E : U → Y → C) (eq : D = E) :
      HEq (transposeBlock MC D ys (us x)) (transposeBlock MC E ys (us x)) := by
    subst E
    rfl
  exact (h _ _ (rawRow_eval (T:=T) vs V P A B x)).trans
    (transpose_map (A x) ys (raggedCell (S:=𝒮) (Z:=𝟘ₐ) (T:=T) (Av x) (J₂).terms Bv) (us x))


theorem actE_over_decode {I X : Type u} {A B : I → C} (p : ∀ t, A t ⟶ B t)
    (G : X → GridExpr I) {P Q : X → C}
    (ea : ∀ x, GridExpr.eval (S:=𝒮) (Z:=𝟘ₐ) A (G x) = P x)
    (eb : ∀ x, GridExpr.eval (S:=𝒮) (Z:=𝟘ₐ) B (G x) = Q x)
    (q : ∀ x, P x ⟶ Q x) (h : ∀ x, HEq (GridExpr.actE (S:=𝒮) (Z:=𝟘ₐ) p (G x)) (q x))
    (l : List X) :
    HEq (GridExpr.actE (S:=𝒮) (Z:=𝟘ₐ) p (GridExpr.over G l)) (act 𝒮 𝟘ₐ q l) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [GridExpr.over, GridExpr.actE, act]
    exact structural_map_heq (S:=𝒮) (ea x) (eb x)
      ((GridExpr.eval_over A G xs).trans (congrArg (fun F => fold 𝒮 𝟘ₐ F xs) (funext ea)))
      ((GridExpr.eval_over B G xs).trans (congrArg (fun F => fold 𝒮 𝟘ₐ F xs) (funext eb)))
      (h x) ih

theorem std_act_map_heq {X Y : Type u} {D E : Y → C} (f : X → Y) (p : ∀ y, D y ⟶ E y) (l : List X) :
    HEq (act 𝒮 𝟘ₐ (fun x => p (f x)) l) (act 𝒮 𝟘ₐ p (l.map f)) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [act]
    exact structural_map_heq (S:=𝒮) rfl rfl (std_fold_map D f xs).symm (std_fold_map E f xs).symm
      (show HEq (p (f x)) (p (f x)) from HEq.rfl) ih

section JointShape
variable (D₀ : X → C → Y → C → C)
set_option quotPrecheck false in
local notation "lab" => fun t : X × U × Y × W => D₀ t.1 (A t.1 t.2.1) t.2.2.1 (B t.2.2.1 t.2.2.2)
set_option quotPrecheck false in
local notation "Fv" => fun x y a => fold 𝒮 𝟘ₐ (D₀ x a y) ((J₂).terms y)
set_option quotPrecheck false in
local notation "Fu" => fun x y => fold 𝒮 𝟘ₐ (Fv x y) ((J₁).terms x)
local notation "Fy" => fun x => fold 𝒮 𝟘ₐ (Fu x) ys

theorem raw_joint_v (x : X) (y : Y) (u : U) :
    GridExpr.eval (S:=𝒮) (Z:=𝟘ₐ) lab (innerQuad vs x y u) = Fv x y (A x u) :=
  (GridExpr.eval_over _ _ _).trans (std_fold_map (D₀ x (A x u) y) (B y) (vs y)).symm

theorem raw_joint_u (x : X) (y : Y) :
    GridExpr.eval (S:=𝒮) (Z:=𝟘ₐ) lab (GridExpr.over (fun u => innerQuad vs x y u) (us x)) = Fu x y :=
  (GridExpr.eval_over _ _ _).trans
    ((congrArg (fun F => fold 𝒮 𝟘ₐ F (us x)) (funext (raw_joint_v vs A B D₀ x y))).trans
      (std_fold_map (Fv x y) (A x) (us x)).symm)

theorem raw_joint_y (x : X) :
    GridExpr.eval (S:=𝒮) (Z:=𝟘ₐ) lab
      (GridExpr.over (fun y => GridExpr.over (fun u => innerQuad vs x y u) (us x)) ys) = Fy x :=
  (GridExpr.eval_over _ _ _).trans
    (congrArg (fun F => fold 𝒮 𝟘ₐ F ys) (funext (raw_joint_u us vs A B D₀ x)))

theorem raw_joint_shape :
    GridExpr.eval (S:=𝒮) (Z:=𝟘ₐ) lab dst = fold 𝒮 𝟘ₐ Fy xs :=
  (GridExpr.eval_over _ _ _).trans
    (congrArg (fun F => fold 𝒮 𝟘ₐ F xs) (funext (raw_joint_y ys us vs A B D₀)))

variable {D₁ : X → C → Y → C → C}
theorem raw_joint_act (p : ∀ x u y v, D₀ x u y v ⟶ D₁ x u y v) :
    HEq (GridExpr.actE (S:=𝒮) (Z:=𝟘ₐ) (fun t : X × U × Y × W =>
        p t.1 (A t.1 t.2.1) t.2.2.1 (B t.2.2.1 t.2.2.2)) dst)
      (act 𝒮 𝟘ₐ (fun x => act 𝒮 𝟘ₐ (fun y =>
        act 𝒮 𝟘ₐ (fun a => act 𝒮 𝟘ₐ (p x a y) ((J₂).terms y)) ((J₁).terms x)) ys) xs) := by
  apply actE_over_decode _ _ (raw_joint_y ys us vs A B D₀) (raw_joint_y ys us vs A B D₁)
  intro x
  apply actE_over_decode _ _ (raw_joint_u us vs A B D₀ x) (raw_joint_u us vs A B D₁ x)
  intro y
  let q := fun a => act 𝒮 𝟘ₐ (p x a y) ((J₂).terms y)
  have h := std_act_map_heq (A x) q (us x)
  refine HEq.trans ?_ h
  apply actE_over_decode _ _ (raw_joint_v vs A B D₀ x y) (raw_joint_v vs A B D₁ x y)
  intro u
  have h' := std_act_map_heq (B y) (p x (A x u) y) (vs y)
  refine HEq.trans ?_ h'
  apply actE_over_decode _ _ (fun _ => rfl) (fun _ => rfl)
  intro v
  rfl
end JointShape


section Native
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (N : GridBinary (symmetricCross (C:=C)) R L) (NR : GatherOuterNat R) (NL : GatherLeftNat L)
variable {I : C} (J : UnitCompat R I) (m : Middle T I)
variable (δ : ∀ x : X, inner (S:=(binary (Additive.ofBraided (C:=C)).sum)) (Z:=(𝟙_ C)) (indexInput A us) x ⟶ I)
variable (δ' : ∀ y : Y, inner (S:=(binary (Additive.ofBraided (C:=C)).sum)) (Z:=(𝟙_ C)) (indexInput B vs) y ⟶ I)
variable (ε : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) V xs ⟶ I) (ε' : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) P ys ⟶ I)

abbrev separateLeafLabels := rawA

abbrev jointLeafLabels (t : X × U × Y × W) : C :=
  T.obj (T.obj (V t.1) (P t.2.2.1)) (T.obj (A t.1 t.2.1) (B t.2.2.1 t.2.2.2))

local notation "Araw" => separateLeafLabels (T:=T) V P A B
local notation "Braw" => jointLeafLabels (T:=T) V P A B

def binaryLeafIso (mi : MiddleInv m) (t : X × U × Y × W) : Araw t ≅ Braw t :=
  let i := mi.cell (V t.1) (A t.1 t.2.1) (P t.2.2.1) (B t.2.2.1 t.2.2.2)
  ⟨m.cell (V t.1) (A t.1 t.2.1) (P t.2.2.1) (B t.2.2.1 t.2.2.2), i.inv, i.hi, i.ih⟩

noncomputable def separateWordAug :
    fold 𝒮 𝟘ₐ Araw (src).leaves ⟶ I :=
  compressGrid Araw src ≫ eqToHom (raw_src_eq (T:=T) xs ys us vs V P A B) ≫
    separateGlobalAug R L J xs ys V P (J₁) (J₂) δ δ' ε ε'

noncomputable def jointWordAug :
    fold 𝒮 𝟘ₐ Braw (dst).leaves ⟶ I :=
  compressGrid Braw dst ≫
    eqToHom (raw_joint_shape xs ys us vs A B (fun x u y v => T.obj (T.obj (V x) (P y)) (T.obj u v))) ≫
    actRect (S:=𝒮) (Z:=𝟘ₐ) xs ys (jointAugRow R L J V P (J₁) (J₂) δ δ') ≫
    jointParentAug R L J xs ys V P ε ε'

set_option backward.isDefEq.respectTransparency false in
include N NR NL in
theorem binary_word_aug_preserving (mi : MiddleInv m)
    (h : MedialLinear m R L) (j : MedialInner m R L)
    (unit_middle : m.cell I I I I ≫ unitCollapse R J = unitCollapse R J) :
    AddressOrder.mapSum additiveStructure Araw (gridOrder circuit) ≫
      act 𝒮 𝟘ₐ (fun t => (binaryLeafIso V P A B m mi t).hom) (dst).leaves ≫
      jointWordAug xs ys us vs V P A B R L J δ δ' ε ε' =
    separateWordAug xs ys us vs V P A B R L J δ δ' ε ε' := by
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
  let b :=
    actRect (S:=𝒮) (Z:=𝟘ₐ) xs ys (jointAugRow R L J V P (J₁) (J₂) δ δ') ≫
      jointParentAug R L J xs ys V P ε ε'
  have ep : G ≫ eqToHom hnew = eqToHom hdst ≫ F :=
    heq_paste hdst hnew (raw_joint_act xs ys us vs A B d₀ leaf)
  have ec : f ≫ eqToHom hdst = eqToHom hsrc ≫ τ :=
    heq_paste hsrc hdst (raw_exchange_heq (T:=T) xs ys us vs V P A B)
  have H :
      separateGlobalAug R L J xs ys V P (J₁) (J₂) δ δ' ε ε' = τ ≫ (F ≫ b) :=
    binary_global_augmentation MC R L N NR NL J m xs ys V P (J₁) (J₂) δ δ' ε ε' h j unit_middle
  unfold separateWordAug jointWordAug
  change _ ≫ act 𝒮 𝟘ₐ p (dst).leaves ≫ (compressGrid Braw dst ≫ eqToHom hnew ≫ b) =
    compressGrid Araw src ≫ eqToHom hsrc ≫ _
  rw [← Category.assoc (act 𝒮 𝟘ₐ p (dst).leaves), compressGrid_natural, Category.assoc,
    ← Category.assoc G, ep]
  simp only [Category.assoc]
  have ca := congrArg (fun d => d ≫ eqToHom hdst ≫ F ≫ b) (compressGrid_order Araw circuit)
  have cb := congrArg (fun d => compressGrid Araw src ≫ d ≫ F ≫ b) ec
  have cc := congrArg (fun d => compressGrid Araw src ≫ eqToHom hsrc ≫ d) H.symm
  simp only [Category.assoc] at ca cb
  exact ca.trans (cb.trans cc)

include N NR NL in
/-- Binary dependent Fubini on the fixed actual native augmented families
presented by the tagged occurrence-first and joint words. This statement
does not assert naturality under variation of the input families. -/
noncomputable def binaryNativeAugIso (mi : MiddleInv m) (hn : (src).leaves.Nodup)
    (h : MedialLinear m R L) (j : MedialInner m R L)
    (unit_middle : m.cell I I I I ≫ unitCollapse R J = unitCollapse R J) :
    NativeAugmentedIso
      (wordAug Araw (src).leaves (separateWordAug xs ys us vs V P A B R L J δ δ' ε ε'))
      (wordAug Braw (dst).leaves (jointWordAug xs ys us vs V P A B R L J δ δ' ε ε')) :=
  wordAugIso Araw Braw (gridOrder circuit) hn (binaryLeafIso V P A B m mi) _ _
    (binary_word_aug_preserving xs ys us vs V P A B R L N NR NL J m δ δ' ε ε'
      mi h j unit_middle)

end Native
end Raw
end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
