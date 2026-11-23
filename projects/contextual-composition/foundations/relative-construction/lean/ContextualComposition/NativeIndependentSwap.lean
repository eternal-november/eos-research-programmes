module
public import ContextualComposition.NativeIndependentSwapChart
@[expose] public section

/-! The independent symmetry on actual augmented objects and the exact
ordered preservation data for its whiskering in a dependent family. -/
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

set_option backward.isDefEq.respectTransparency false in
theorem swapRawLeftCell_read :
    HEq (swapRawLeftCell xs ys R L A B p q)
      (rectWordChart (crossLabel T A B) xs ys ≫ independentCell R L A B xs ys p q) := by
  let F := crossLabel T A B
  let L₀ : fold 𝒮 Zₐ (fun x => fold 𝒮 Zₐ (fun y => F (x,y)) ys) xs ⟶ T.obj a b :=
    independentCell R L A B xs ys p q
  change HEq (compressGrid F (rectPairExpr xs ys) ≫ eqToHom (rectPairExpr_eval F xs ys) ≫ L₀)
    (rectWordChart F xs ys ≫ L₀)
  rw [reassoc_of% rectPairExpr_chart F xs ys]
  exact hom_source_pin_heq _ _

omit [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] in
theorem swapGridOut_word :
    (swapGridOut xs ys).leaves.map Prod.swap = ys.product xs := by
  rw [swapGridOut_retag, retagGrid_leaves, rectPairExpr_leaves]
  exact equiv_word_read (Equiv.prodComm X Y) (ys.product xs)

set_option backward.isDefEq.respectTransparency false in
theorem swapRawRightCell_read :
    HEq (swapRawRightCell xs ys R L A B p q)
      (rectWordChart (crossLabel T B A) ys xs ≫ independentCell R L B A ys xs q p) := by
  let K := crossLabel T B A
  let H := fun z : X × Y => T.obj (B z.2) (A z.1)
  let col := swapGridOut xs ys
  let t := rectPairExpr ys xs
  let pinCol := swapGridOut_retag xs ys
  let h := (retagGrid_eval H Prod.swap t).trans (rectPairExpr_eval K ys xs)
  let α := (congrArg (GridExpr.eval (S:=𝒮) (Z:=Zₐ) H) pinCol).trans h
  have pin : eqToHom (swapGridOut_eval xs ys H) = eqToHom α := rfl
  have eq : HEq (compressGrid H col ≫ eqToHom α) (compressGrid H (retagGrid Prod.swap t) ≫ eqToHom h) := by
    have hh {s t' : GridExpr (X × Y)} (e : s = t')
        (h : GridExpr.eval (S:=𝒮) (Z:=Zₐ) H t' = fold 𝒮 Zₐ (fun y => fold 𝒮 Zₐ (fun x => H (x,y)) xs) ys) :
        HEq (compressGrid H s ≫ eqToHom ((congrArg (GridExpr.eval (S:=𝒮) (Z:=Zₐ) H) e).trans h))
          (compressGrid H t' ≫ eqToHom h) := by subst t'; rfl
    exact hh pinCol h
  let e := congrArg (fold 𝒮 Zₐ H) (congrArg GridExpr.leaves pinCol)
  let L₀ : fold 𝒮 Zₐ (fun y => fold 𝒮 Zₐ (fun x => K (y,x)) xs) ys ⟶ T.obj b a :=
    independentCell R L B A ys xs q p
  let hC : GridExpr.eval (S:=𝒮) (Z:=Zₐ) H col ⟶ fold 𝒮 Zₐ (fun y => fold 𝒮 Zₐ (fun x => K (y,x)) xs) ys := eqToHom α
  change HEq (compressGrid H col ≫ hC ≫ L₀) _
  rw [← Category.assoc]
  change HEq ((compressGrid H col ≫ eqToHom α) ≫ L₀) _
  refine (structural_seq_heq (K:=coeff (C:=C)) e rfl rfl eq (HEq.rfl : HEq L₀ L₀)).trans ?_
  have h₀ := compressGrid_retag H Prod.swap t
  have h₁ := rectPairExpr_chart K ys xs
  change HEq ((compressGrid H (retagGrid Prod.swap t) ≫ eqToHom h) ≫ L₀) _
  unfold h
  let e₀ := retagGrid_eval H Prod.swap t
  let e₁ := rectPairExpr_eval K ys xs
  change HEq ((compressGrid H (retagGrid Prod.swap t) ≫ eqToHom (e₀.trans e₁)) ≫ L₀) _
  rw [← eqToHom_trans e₀ e₁, ← Category.assoc (compressGrid H (retagGrid Prod.swap t)), h₀]
  simp only [Category.assoc]
  let j := (congrArg (fold 𝒮 Zₐ H) (retagGrid_leaves Prod.swap t)).trans (std_fold_map H Prod.swap t.leaves)
  change HEq (eqToHom j ≫ compressGrid K t ≫ eqToHom e₁ ≫ L₀) _
  rw [reassoc_of% h₁, eqToHom_trans_assoc]
  exact hom_source_pin_heq _ _

variable {I : C} (J : UnitCompat R I)
variable (swap_unit : P.swap I I ≫ J.ρ I = J.ρ I)
variable (ι : ∀ a b, IsIso (P.swap a b))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2300000 in
noncomputable def independentSwapReadComparison
    (p : fold 𝒮 Zₐ A xs ⟶ I) (q : fold 𝒮 Zₐ B ys ⟶ I) :
    WordAugReadComparison (crossLabel T A B) (crossLabel T B A) (xs.product ys) (ys.product xs)
      (rectangularWordAugCell R L (J.ρ I) A B xs ys p q) (rectangularWordAugCell R L (J.ρ I) B A ys xs q p) := by
  let f := Equiv.prodComm X Y
  let F := crossLabel T A B
  let G := crossLabel T B A
  let u := (rectPairExpr xs ys).leaves
  let v := (swapGridOut xs ys).leaves
  let a := rectangularWordAugCell R L (J.ρ I) A B xs ys p q
  let b := rectangularWordAugCell R L (J.ρ I) B A ys xs q p
  let a₀ := swapRawLeftCell xs ys R L A B p q ≫ J.ρ I
  let b₀ := swapRawRightCell xs ys R L A B p q ≫ J.ρ I
  let φ (z : X × Y) : F z ≅ G (f z) := by
    let _ := ι (A z.1) (B z.2)
    exact asIso (P.swap (A z.1) (B z.2))
  have hu : u.map id = xs.product ys := (List.map_id u).trans (rectPairExpr_leaves xs ys)
  have hv : v.map (f ∘ id) = ys.product xs := swapGridOut_word xs ys
  let eu := (std_fold_map F id u).symm.trans (congrArg (fold 𝒮 Zₐ F) hu)
  let ev := (std_fold_map G f v).symm.trans (congrArg (fold 𝒮 Zₐ G) hv)
  have ha : HEq a a₀ := by
    have h := (structural_seq_heq (K:=coeff (C:=C)) eu rfl rfl
    (swapRawLeftCell_read R L A B xs ys p q) (HEq.rfl : HEq (J.ρ I) (J.ρ I))).symm
    exact (heq_of_eq (Category.assoc _ _ _).symm).trans h
  have hb : HEq b b₀ := by
    have h := (structural_seq_heq (K:=coeff (C:=C)) ev rfl rfl
    (swapRawRightCell_read R L A B xs ys p q) (HEq.rfl : HEq (J.ρ I) (J.ρ I))).symm
    exact (heq_of_eq (Category.assoc _ _ _).symm).trans h
  let o := gridOrder (swapGrid xs ys)
  have h := swapRawCell_preserves xs ys R L P Q N A B p q
  have k := congrArg (fun x => x ≫ J.ρ I) h
  simp only [Category.assoc] at k
  rw [swap_unit] at k
  exact WordAugReadComparison.ofScalarOrder f id (xs.product ys) (ys.product xs) u v hu hv φ a b
    a₀ b₀ ha hb o k

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
