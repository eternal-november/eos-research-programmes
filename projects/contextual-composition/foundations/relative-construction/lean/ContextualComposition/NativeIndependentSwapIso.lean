module
public import ContextualComposition.NativeWordReadIso
public import ContextualComposition.NativeFubiniSymmetryLaw
@[expose] public section

/-! Actual independent augmented symmetry with the exact swap of raw
addresses. The coefficient braid is not inferred from the carrier. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [cat : Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)
variable {T : Bi (coeff (C:=C))} {I : C}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (J : UnitCompat R I)
variable (P : TensorPrimitive T) (Q : PrimitiveLinearity R L P)
variable (N : GridBinary (symmetricCross (C:=C)) R L)
variable (swap_unit : P.swap I I ≫ J.ρ I = J.ρ I)
variable (ι : ∀ a b, IsIso (P.swap a b))
variable {X Y : Type u} (A : X → C) (B : Y → C)
variable (xs : List X) (ys : List Y)
variable (p : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) A xs ⟶ I)
variable (q : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) B ys ⟶ I)

set_option backward.isDefEq.respectTransparency false in
noncomputable def independentSwapIso (hx : xs.Nodup) (hy : ys.Nodup) :
    NativeAugmentedIso
      (independentAug R L (J.ρ I) (wordAug A xs p) (wordAug B ys q))
      (independentAug R L (J.ρ I) (wordAug B ys q) (wordAug A xs p)) :=
  let o := independentSwapReadComparison R L P Q N A B xs ys J swap_unit ι p q
  (o.toIso (nodup_product_word hx hy)).retarget
    (independentAug_ordered_eq R L (J.ρ I) A B xs ys p q).symm
    (independentAug_ordered_eq R L (J.ρ I) B A ys xs q p).symm

set_option backward.isDefEq.respectTransparency false in
theorem independentSwapIso_trace (hx : xs.Nodup) (hy : ys.Nodup) :
    let F := (rawWordFrame A xs hx).tensor T (rawWordFrame B ys hy)
    let G := ((rawWordFrame B ys hy).tensor T (rawWordFrame A xs hx)).relabel
      (Equiv.prodComm Y X) (Equiv.prodComm Y X).injective (fun z => T.obj (B z.2) (A z.1)) (fun _ => rfl)
    RawSingletonTrace F G (fun z => P.swap (A z.1) (B z.2))
      (independentSwapIso R L J P Q N swap_unit ι A B xs ys p q hx hy).hom.native := by
  intro F G
  let H := crossLabel T A B
  let K := crossLabel T B A
  let Z := fun z : X × Y => T.obj (B z.2) (A z.1)
  let o := independentSwapReadComparison R L P Q N A B xs ys J swap_unit ι p q
  let hn := nodup_product_word hx hy
  let hm := nodup_product_word hy hx
  let F₀ := rawWordFrame H (xs.product ys) hn
  let G₀ := (rawWordFrame K (ys.product xs) hm).relabel (Equiv.prodComm Y X) (Equiv.prodComm Y X).injective Z (fun _ => rfl)
  let e := independentFamily_word (T:=T) A B xs ys
  let d := independentFamily_word (T:=T) B A ys xs
  have r (j : Fin _) : F.read j = F₀.read (Fin.cast (congrArg Family.n e) j) :=
    frame_tensor_read_cast (rawWordFrame A xs hx) (rawWordFrame B ys hy) rfl rfl (fun _ => rfl) (fun _ => rfl) j
  have s (j : Fin _) : G.read j = G₀.read (Fin.cast (congrArg Family.n d) j) :=
    congrArg (Equiv.prodComm Y X)
      (frame_tensor_read_cast (rawWordFrame B ys hy) (rawWordFrame A xs hx) rfl rfl (fun _ => rfl) (fun _ => rfl) j)
  have tr : RawSingletonTrace F₀ G₀ (fun z => P.swap (A z.1) (B z.2)) (o.toIso hn).hom.native :=
    (o.toIso_trace hn hm).changeFrame (fun _ => rfl) (fun _ => rfl) (fun _ => HEq.rfl)
  have k : HEq (o.toIso hn).hom.native
      (independentSwapIso R L J P Q N swap_unit ι A B xs ys p q hx hy).hom.native := by
    unfold independentSwapIso
    exact (NativeAugmentedIso.retarget_native_heq _ _ _).symm
  exact tr.retarget e.symm d.symm k (rawFrame_read_reverse F F₀ e r)
    (rawFrame_read_reverse G G₀ d s) (fun _ => HEq.rfl)

set_option backward.isDefEq.respectTransparency false in
omit [MonoidalCategory C] [SymmetricCategory C] in
theorem standardSwapUnit (mul : MonoidalCategory C) (br : @BraidedCategory C cat mul)
    {S : Bi (coeff (C:=C))} {Z : C}
    (r : Gather S (binary (@Binary.ofMonoidal C cat mul)) Z)
    (j : UnitCompat r (@MonoidalCategoryStruct.tensorUnit C cat mul.toMonoidalCategoryStruct))
    (h : ∀ a : C, j.ρ a = (@MonoidalCategoryStruct.rightUnitor C cat mul.toMonoidalCategoryStruct a).hom) :
    (@tensorPrimitives C cat mul br).swap _ _ ≫ j.ρ _ = j.ρ _ :=
  standardDepLeftUnit_agrees_at_unit mul br r j h

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
