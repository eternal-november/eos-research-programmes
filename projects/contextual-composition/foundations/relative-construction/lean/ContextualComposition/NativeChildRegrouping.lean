module
public import ContextualComposition.NativeWholeContinuation

@[expose] public section

/-! Move each actually prescribed child-target cell from child-major
parent aggregation to parent-major whole continuation aggregation. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre
universe u v w
variable {C : Type u} {K : Coeff.{u,v} C} {S T : Bi K} {Z : C}
variable (M : AddCross S Z) (R : Gather S T Z) (L : LeftGather S T Z)
variable (N : GridBinary M R L) (NL : GatherLeftNat L)
variable {X Y : Type w} (V : X → C) (W : Y → C) (A : X → Y → C)
variable (xs : List X) (ys : List Y)
variable (p : ∀ x y, K.Hom (A x y) (T.obj (V x) (W y)))
variable {a : C} (α : K.Hom (fold S Z V xs) a)

/-- Child-major: apply every opaque child-target cell, gather each target
child's parent fibre using the same opaque parent map, then gather the
ordered target continuations at the new parent. -/
def childMajorParentGather :=
  K.seq (act S Z (fun y =>
    K.seq (act S Z (fun x => p x y) xs)
      (K.seq (gather R V (W y) xs) (T.map α (K.id (W y))))) ys)
    (Lin.collect (Lin.left L a) W ys)

/-- Parent-major: apply every opaque child-target cell and gather its
target continuation at the original parent; the parent map is last. -/
def parentMajorChildGather :=
  K.seq (act S Z (fun x =>
    K.seq (act S Z (p x) ys) (Lin.collect (Lin.left L (V x)) W ys)) xs)
    (K.seq (gather R V (fold S Z W ys) xs) (T.map α (K.id (fold S Z W ys))))

include N NL in
theorem child_parent_regrouping :
    K.seq (transposeBlock M A ys xs) (childMajorParentGather R L V W A xs ys p α) =
      parentMajorChildGather R L V W A xs ys p α := by
  let b := fold S Z V xs
  let u := T.map α (K.id (fold S Z W ys))
  let r := act S Z (fun y => act S Z (fun x => p x y) xs) ys
  let s := act S Z (fun y => gather R V (W y) xs) ys
  let g := Lin.collect (Lin.left L b) W ys
  let h := act S Z (fun y => T.map α (K.id (W y))) ys
  let j := Lin.collect (Lin.left L a) W ys
  have e : K.seq h j = K.seq g u := ((NL.outer α).collect W ys).symm
  have e₁ : childMajorParentGather R L V W A xs ys p α = K.seq r (K.seq s (K.seq g u)) := by
    unfold childMajorParentGather
    rw [← act_seq, ← act_seq]
    simp only [K.assoc]
    change K.seq r (K.seq s (K.seq h j)) = _
    rw [e]
  let r' := act S Z (fun x => act S Z (p x) ys) xs
  let t := transposeBlock M (fun x y => T.obj (V x) (W y)) ys xs
  have e₂ : K.seq (transposeBlock M A ys xs) r = K.seq r' t :=
    (transposeBlock_natural M p xs ys).symm
  have e₃ : K.seq t (K.seq s g) = rowGather R L V W xs ys :=
    row_col_gather M R L N V W xs ys
  rw [e₁, ← K.assoc (transposeBlock M A ys xs), e₂]
  simp only [K.assoc]
  rw [← K.assoc s, ← K.assoc t, e₃]
  unfold parentMajorChildGather rowGather
  rw [← act_seq]
  simp only [K.assoc]

  rfl

end ContextualComposition.NativeFinitePush.DependentFibre

namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v w
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "MC" => symmetricCross (C:=C)
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
variable {I X Y : Type u} (A : I → C) (P : X → Y → GridExpr I)
variable (xs : List X) (ys : List Y)
local notation "Q" => fun x y => GridExpr.eval (S:=𝒮) (Z:=Zₐ) A (P x y)
local notation "rowExpr" => GridExpr.over (fun x => GridExpr.over (P x) ys) xs
local notation "colExpr" => GridExpr.over (fun y => GridExpr.over (fun x => P x y) xs) ys

theorem rowMatrix_pin :
    GridExpr.eval (S:=𝒮) (Z:=Zₐ) A (rowExpr) =
      fold 𝒮 Zₐ (fun x => fold 𝒮 Zₐ (Q x) ys) xs := by
  rw [GridExpr.eval_over]
  congr 1
  funext x
  exact GridExpr.eval_over _ _ _

theorem colMatrix_pin :
    GridExpr.eval (S:=𝒮) (Z:=Zₐ) A (colExpr) =
      fold 𝒮 Zₐ (fun y => fold 𝒮 Zₐ (fun x => Q x y) xs) ys := by
  rw [GridExpr.eval_over]
  congr 1
  funext y
  exact GridExpr.eval_over _ _ _

set_option backward.isDefEq.respectTransparency false in
theorem flat_child_parent_regrouping {T : Bi (coeff (C:=C))}
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ) (N : GridBinary MC R L) (NL : GatherLeftNat L)
    (V : X → C) (W : Y → C) (p : ∀ x y, Q x y ⟶ T.obj (V x) (W y))
    {a : C} (α : fold 𝒮 Zₐ V xs ⟶ a) :
    AddressOrder.mapSum additiveStructure A (gridOrder (GridCircuit.transpose P ys xs)) ≫
      compressGrid A (colExpr) ≫ eqToHom (colMatrix_pin A P xs ys) ≫
        childMajorParentGather R L V W Q xs ys p α =
    compressGrid A (rowExpr) ≫ eqToHom (rowMatrix_pin A P xs ys) ≫
      parentMajorChildGather R L V W Q xs ys p α := by
  let t := GridCircuit.transpose P ys xs
  let rt := eqToHom (rowMatrix_pin A P xs ys)
  let ct := eqToHom (colMatrix_pin A P xs ys)
  let q := childMajorParentGather R L V W Q xs ys p α
  let r := parentMajorChildGather R L V W Q xs ys p α
  let d := transposeBlock MC Q ys xs
  have e : GridCircuit.eval MC A t ≫ ct = rt ≫ d :=
    heq_paste (rowMatrix_pin A P xs ys) (colMatrix_pin A P xs ys) (GridCircuit.transpose_eval MC A P ys xs)
  have h : d ≫ q = r := child_parent_regrouping MC R L N NL V W Q xs ys p α
  have s := compressGrid_order A t
  change AddressOrder.mapSum additiveStructure A (gridOrder t) ≫ compressGrid A colExpr ≫ ct ≫ q =
    compressGrid A rowExpr ≫ rt ≫ r
  rw [← Category.assoc (AddressOrder.mapSum additiveStructure A (gridOrder t)), s]
  simp only [Category.assoc]
  rw [reassoc_of% e, h]

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
