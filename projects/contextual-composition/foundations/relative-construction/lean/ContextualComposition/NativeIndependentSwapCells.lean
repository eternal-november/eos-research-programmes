module
public import ContextualComposition.NativeIndependentSwap
@[expose] public section

/-! The rectangular swap commutes with arbitrary whole selected cells, not only with global augmentations. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)

variable {T : Bi (coeff (C:=C))}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (P : TensorPrimitive T) (Q : PrimitiveLinearity R L P)
variable (N : GridBinary (symmetricCross (C:=C)) R L)
variable {X Y : Type u} (A : X → C) (B : Y → C) (xs : List X) (ys : List Y)
variable {a b : C}
variable (p : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) A xs ⟶ a)
variable (q : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) B ys ⟶ b)

/-- Chart compression followed by an arbitrary whole cell and output map. -/
noncomputable def swapRectCell {z : C} (g : T.obj a b ⟶ z) :=
  rectWordChart (crossLabel T A B) xs ys ≫ independentCell R L A B xs ys p q ≫ g

variable (ι : ∀ a b, IsIso (P.swap a b))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2300000 in
noncomputable def independentSwapCellComparison :
    WordAugReadComparison (crossLabel T A B) (crossLabel T B A) (xs.product ys) (ys.product xs)
      (swapRectCell R L A B xs ys p q (P.swap a b))
      (swapRectCell R L B A ys xs q p (𝟙 (T.obj b a))) := by
  let f := Equiv.prodComm X Y
  let F := crossLabel T A B
  let G := crossLabel T B A
  let u := (rectPairExpr xs ys).leaves
  let v := (swapGridOut xs ys).leaves
  let left := swapRectCell R L A B xs ys p q (P.swap a b)
  let right := swapRectCell R L B A ys xs q p (𝟙 (T.obj b a))
  let a₀ := swapRawLeftCell xs ys R L A B p q ≫ P.swap a b
  let b₀ := swapRawRightCell xs ys R L A B p q
  let φ (z : X × Y) : F z ≅ G (f z) := by
    let _ := ι (A z.1) (B z.2)
    exact asIso (P.swap (A z.1) (B z.2))
  have hu : u.map id = xs.product ys := (List.map_id u).trans (rectPairExpr_leaves xs ys)
  have hv : v.map (f ∘ id) = ys.product xs := swapGridOut_word xs ys
  let eu := (std_fold_map F id u).symm.trans (congrArg (fold 𝒮 Zₐ F) hu)
  let ev := (std_fold_map G f v).symm.trans (congrArg (fold 𝒮 Zₐ G) hv)
  have ha : HEq left a₀ := by
    have h := (structural_seq_heq (K:=coeff (C:=C)) eu rfl rfl
    (swapRawLeftCell_read R L A B xs ys p q) (HEq.rfl : HEq (P.swap a b) (P.swap a b))).symm
    exact (heq_of_eq (Category.assoc _ _ _).symm).trans h
  have hb : HEq right b₀ := by
    unfold right swapRectCell
    simp only [Category.comp_id]
    exact (swapRawRightCell_read R L A B xs ys p q).symm
  exact WordAugReadComparison.ofScalarOrder f id (xs.product ys) (ys.product xs) u v hu hv φ left right
    a₀ b₀ ha hb (gridOrder (swapGrid xs ys)) (swapRawCell_preserves xs ys R L P Q N A B p q)

set_option backward.isDefEq.respectTransparency false in
theorem addressed_mapSum_heq {K : X → C} {u v u' v' : List X}
    (h : u = u') (k : v = v') (hn : u.Nodup)
    (a : AddressOrder X u v) (b : AddressOrder X u' v') :
    HEq (AddressOrder.mapSum additiveStructure K a) (AddressOrder.mapSum additiveStructure K b) := by
  subst u'
  subst v'
  exact heq_of_eq (tagged_permutation_coherent K hn a b)

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
