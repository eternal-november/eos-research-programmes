module
public import ContextualComposition.NativeIndependentSwapGather
@[expose] public section

/-! Separately decode the additive rectangular transposition and the
multiplicative braided coefficient comparison. The raw transpose is a
genuine order change, rather than mere renaming of positions. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C

variable {X Y : Type u} (xs : List X) (ys : List Y)
def swapGrid : GridCircuit (X × Y) (rectPairExpr xs ys)
    (GridExpr.over (fun y => GridExpr.over (fun x => GridExpr.leaf (x,y)) xs) ys) :=
  GridCircuit.transpose (fun x y => GridExpr.leaf (x,y)) ys xs

def swapGridOut := GridExpr.over (fun y => GridExpr.over (fun x => GridExpr.leaf (x,y)) xs) ys

set_option backward.isDefEq.respectTransparency false in
theorem swapGridOut_retag :
    swapGridOut xs ys = retagGrid Prod.swap (rectPairExpr ys xs) := by
  unfold swapGridOut rectPairExpr
  simp only [retagGrid_over, retagGrid]
  rfl

theorem swapGridOut_eval (A : X × Y → C) :
    GridExpr.eval (S:=𝒮) (Z:=Zₐ) A (swapGridOut xs ys) =
      fold 𝒮 Zₐ (fun y => fold 𝒮 Zₐ (fun x => A (x,y)) xs) ys :=
  colMatrix_pin A (fun x y => GridExpr.leaf (x,y)) xs ys

theorem swapGridOut_act {A B : X × Y → C} (p : ∀ t, A t ⟶ B t) :
    HEq (GridExpr.actE (S:=𝒮) (Z:=Zₐ) p (swapGridOut xs ys))
      (act 𝒮 Zₐ (fun y => act 𝒮 Zₐ (fun x => p (x,y)) xs) ys) := by
  apply actE_over_decode p (fun y => GridExpr.over (fun x => GridExpr.leaf (x,y)) xs)
    (fun y => GridExpr.eval_over A _ xs) (fun y => GridExpr.eval_over B _ xs)
  intro y
  exact actE_over_decode p (fun x => GridExpr.leaf (x,y)) (fun _ => rfl) (fun _ => rfl)
    (fun x => p (x,y)) (fun _ => HEq.rfl) xs

variable {T : Bi (coeff (C:=C))}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (P : TensorPrimitive T) (Q : PrimitiveLinearity R L P)
variable (N : GridBinary (symmetricCross (C:=C)) R L)
variable (A : X → C) (B : Y → C)
variable {a b : C}
variable (p : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) A xs ⟶ a)
variable (q : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) B ys ⟶ b)
local notation "F" => crossLabel T A B
set_option quotPrecheck false in
local notation "H" => (fun z : X × Y => T.obj (B z.2) (A z.1))
local notation "row" => rectPairExpr xs ys
local notation "col" => swapGridOut xs ys

def swapRawLeftCell :=
  compressGrid F row ≫ eqToHom (rectPairExpr_eval F xs ys) ≫ independentCell R L A B xs ys p q

def swapRawRightCell :=
  compressGrid H col ≫ eqToHom (swapGridOut_eval xs ys H) ≫ independentCell R L B A ys xs q p

set_option backward.isDefEq.respectTransparency false in
include Q N in
theorem swapRawCell_preserves :
    AddressOrder.mapSum additiveStructure F (gridOrder (swapGrid xs ys)) ≫
      act 𝒮 Zₐ (fun z : X × Y => P.swap (A z.1) (B z.2)) (col).leaves ≫
      swapRawRightCell xs ys R L A B p q =
    swapRawLeftCell xs ys R L A B p q ≫ P.swap a b := by
  let s (z : X × Y) : F z ⟶ H z := P.swap (A z.1) (B z.2)
  let t := swapGrid xs ys
  let a₀ := eqToHom (rectPairExpr_eval F xs ys)
  let b₀ := eqToHom (swapGridOut_eval xs ys F)
  let b₁ := eqToHom (swapGridOut_eval xs ys H)
  let mc := GridCircuit.eval (symmetricCross (C:=C)) F t
  let τ := transposeBlock (symmetricCross (C:=C)) (fun x y => T.obj (A x) (B y)) ys xs
  let g := act 𝒮 Zₐ (fun y => act 𝒮 Zₐ (fun x => s (x,y)) xs) ys
  let nc := GridExpr.actE (S:=𝒮) (Z:=Zₐ) s col
  let L₀ := independentCell R L A B xs ys p q
  let L₁ := independentCell R L B A ys xs q p
  have h₀ : act 𝒮 Zₐ s (col).leaves ≫ compressGrid H col =
      compressGrid F col ≫ nc := compressGrid_natural s col
  have h₁ : AddressOrder.mapSum additiveStructure F (gridOrder t) ≫ compressGrid F col =
      compressGrid F row ≫ mc := compressGrid_order F t
  have h₂ : nc ≫ b₁ = b₀ ≫ g := heq_paste (swapGridOut_eval xs ys F) (swapGridOut_eval xs ys H)
    (swapGridOut_act xs ys s)
  have h₃ : mc ≫ b₀ = a₀ ≫ τ := heq_paste (rectPairExpr_eval F xs ys) (swapGridOut_eval xs ys F)
    (GridCircuit.transpose_eval (symmetricCross (C:=C)) F (fun x y => GridExpr.leaf (x,y)) ys xs)
  have h₄ : τ ≫ g ≫ L₁ = L₀ ≫ P.swap a b :=
    (independentCell_swap_transposed R L P A B xs ys Q N p q).symm
  change AddressOrder.mapSum additiveStructure F (gridOrder t) ≫ act 𝒮 Zₐ s (col).leaves ≫
      (compressGrid H col ≫ b₁ ≫ L₁) =
    (compressGrid F row ≫ a₀ ≫ L₀) ≫ P.swap a b
  simp only [Category.assoc]
  rw [reassoc_of% h₀, reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, h₄]

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
