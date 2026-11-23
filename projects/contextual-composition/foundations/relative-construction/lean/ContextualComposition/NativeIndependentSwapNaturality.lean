module
public import ContextualComposition.NativeIndependentSwapCells
public import ContextualComposition.NativeIndependentSwapIso
@[expose] public section

/-! Naturality of the original independent symmetry through arbitrary
whole selected cells. -/
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
variable (ι : ∀ a b, IsIso (P.swap a b))
variable {X Y X' Y' : Type u} [DecidableEq X'] [DecidableEq Y']
variable {xs : List X} {ys : List Y} {xs' : List X'} {ys' : List Y'}
variable (f : X → X') (g : Y → Y')
variable (A : X → C) (B : Y → C) (A' : X' → C) (B' : Y' → C)
variable (p : ∀ x ∈ xs', fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C)
  A (wordFibre xs f x) ⟶ A' x)
variable (q : ∀ y ∈ ys', fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C)
  B (wordFibre ys g y) ⟶ B' y)

local notation "r" => Equiv.prodComm Y X
local notation "s" => Equiv.prodComm Y' X'
local notation "F" => Prod.map f g
local notation "G" => Prod.map g f
local notation "ab" => crossLabel T A B
local notation "ba" => crossLabel T B A
local notation "ab'" => crossLabel T A' B'
local notation "ba'" => crossLabel T B' A'
set_option quotPrecheck false in
local notation "us" => xs.product ys
set_option quotPrecheck false in
local notation "us'" => xs'.product ys'
set_option quotPrecheck false in
local notation "vs" => (ys.product xs).map r
set_option quotPrecheck false in
local notation "vs'" => (ys'.product xs').map s
set_option quotPrecheck false in
local notation "srcSwap" => (fun z : X × Y => P.swap (A z.1) (B z.2))
set_option quotPrecheck false in
local notation "tgtSwap" => (fun z : X' × Y' => P.swap (A' z.1) (B' z.2))
local notation "lp" => wordProductCell R L f g A B A' B' p q
local notation "rp" => wordProductCell R L g f B A B' A' q p
set_option quotPrecheck false in
local notation "rpRead" => retagWordCell r s G F (fun _ => rfl)
  (rfl : (ys.product xs).map r = vs) (rfl : (ys'.product xs').map s = vs')
  (ba ∘ (r).symm) (ba' ∘ (s).symm) rp

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3000000 in
include Q N ι in
theorem independentSwap_selected_cell (hx : xs.Nodup) (hy : ys.Nodup)
    (o : AddressOrder (X × Y) (xs.product ys) ((ys.product xs).map (Equiv.prodComm Y X)))
    (z : X' × Y') (hz : z ∈ us') (hw : z ∈ vs') :
    lp z hz ≫ tgtSwap z =
      AddressOrder.mapSum additiveStructure ab (wordFibreOrder F o z) ≫
        act 𝒮 Zₐ srcSwap (wordFibre vs F z) ≫ rpRead z hw := by
  let x := z.1
  let y := z.2
  let h := (dependentWord_mem xs' (fun _ => ys') z).mp hz
  let u := wordFibre xs f x
  let v := wordFibre ys g y
  let a := p x h.1
  let b := q y h.2
  let c := independentSwapCellComparison R L P Q N A B u v a b ι
  have cl : (wordFibre us F z) = u.product v := product_word_fibre xs ys f g z
  have cr : wordFibre vs F z = (v.product u).map r :=
    (retag_wordFibre r s G F (fun _ => rfl) ((s).symm z)).symm.trans
      (congrArg (List.map r) (product_word_fibre ys xs g f ((s).symm z)))
  have hL : HEq (lp z hz ≫ tgtSwap z) (swapRectCell R L A B u v a b (tgtSwap z)) := by
    unfold wordProductCell swapRectCell
    simp only [Category.assoc]
    exact hom_source_pin_heq _ _
  have hR : HEq (rpRead z hw) (swapRectCell R L B A v u b a (𝟙 (T.obj (B' y) (A' x)))) := by
    have h' : (s).symm z ∈ ys'.product xs' := (dependentWord_mem ys' (fun _ => xs') _).mpr ⟨h.2,h.1⟩
    have k : HEq (rpRead z hw) (rp ((s).symm z) h') :=
      retagWordCell_heq r s G F (fun _ => rfl) rfl rfl (ba ∘ (r).symm) (ba' ∘ (s).symm) rp
        ((s).symm z) h' hw
    unfold wordProductCell swapRectCell
    simp only [Category.comp_id]
    exact k.trans (hom_source_pin_heq _ _)
  have hC := c.preserves
  change AddressOrder.mapSum additiveStructure ab c.order ≫
    act 𝒮 Zₐ srcSwap ((v.product u).map r) ≫ eqToHom _ ≫
      swapRectCell R L B A v u b a (𝟙 (T.obj (B' y) (A' x))) =
    swapRectCell R L A B u v a b (tgtSwap z) at hC
  have hN : (wordFibre us F z).Nodup :=
    List.filter_sublist.nodup (nodup_product_word hx hy)
  have e := congrArg (fold 𝒮 Zₐ ab) cl
  have d := congrArg (fold 𝒮 Zₐ ab) cr
  have d' := congrArg (fold 𝒮 Zₐ (ba ∘ (r).symm)) cr
  have hSum := addressed_mapSum_heq (K:=ab) cl cr hN (wordFibreOrder F o z) c.order
  have hAct : HEq (act 𝒮 Zₐ srcSwap (wordFibre vs F z))
      (act 𝒮 Zₐ srcSwap ((v.product u).map r)) := by rw [cr]
  have hHead := structural_seq_heq (K:=coeff (C:=C)) e d d' hSum hAct
  let pin := (std_fold_map ba (r).symm ((v.product u).map r)).symm.trans
    (congrArg (fold 𝒮 Zₐ ba) (equiv_word_read (r).symm (v.product u)))
  let tail := swapRectCell R L B A v u b a (𝟙 (T.obj (B' y) (A' x)))
  have hTail : HEq (rpRead z hw) (eqToHom pin ≫ tail) :=
    hR.trans (hom_source_pin_heq pin tail).symm
  have hAll := structural_seq_heq (K:=coeff (C:=C)) e d' rfl hHead hTail
  refine eq_of_heq (hL.trans ((heq_of_eq hC.symm).trans ?_))
  change HEq ((AddressOrder.mapSum additiveStructure ab (wordFibreOrder F o z) ≫
    act 𝒮 Zₐ srcSwap (wordFibre vs F z)) ≫ rpRead z hw)
    ((AddressOrder.mapSum additiveStructure ab c.order ≫
      act 𝒮 Zₐ srcSwap ((v.product u).map r)) ≫ (eqToHom pin ≫ tail)) at hAll
  simpa only [Category.assoc] using hAll.symm

variable (hf : ∀ a ∈ xs, f a ∈ xs') (hg : ∀ a ∈ ys, g a ∈ ys')
variable (hx : xs.Nodup) (hy : ys.Nodup) (hx' : xs'.Nodup) (hy' : ys'.Nodup)
variable {I : C} (J : UnitCompat R I) (swap_unit : P.swap I I ≫ J.ρ I = J.ρ I)
variable (ax : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) A xs ⟶ I)
variable (ay : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) B ys ⟶ I)
variable (bx : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) A' xs' ⟶ I)
variable (by' : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) B' ys' ⟶ I)

set_option quotPrecheck false in
local notation "pNative" => wordNativeMap f hf hx' A A' (fun j => p xs'[j] (List.getElem_mem _))
set_option quotPrecheck false in
local notation "qNative" => wordNativeMap g hg hy' B B' (fun j => q ys'[j] (List.getElem_mem _))
local notation "originalL" => independentNativeWordMap T pNative qNative R L
local notation "originalR" => independentNativeWordMap T qNative pNative R L
local notation "swapX" => independentSwapIso R L J P Q N swap_unit ι A B xs ys ax ay hx hy
local notation "swapY" => independentSwapIso R L J P Q N swap_unit ι A' B' xs' ys' bx by' hx' hy'
local notation "cmpX" => independentSwapReadComparison R L P Q N A B xs ys J swap_unit ι ax ay
local notation "cmpY" => independentSwapReadComparison R L P Q N A' B' xs' ys' J swap_unit ι bx by'

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3500000 in
theorem independentSwap_original_native_square :
    (originalL).comp (swapY).hom.native = (swapX).hom.native.comp originalR := by
  let hfl := wordProduct_support f g hf hg
  let hfr := wordProduct_support g f hg hf
  let hL := nodup_product_word hx hy
  let hL' := nodup_product_word hx' hy'
  let hR' := nodup_product_word hy' hx'
  let c := cmpX
  let d := cmpY
  let o : AddressOrder (X × Y) us vs := c.order
  let o' : AddressOrder (X' × Y') us' vs' := d.order
  let v := retag_word_support r s G F (fun _ => rfl) (rfl : (ys.product xs).map r = vs)
    (rfl : (ys'.product xs').map s = vs') hfr
  let l := wordNativeMap F hfl hL' ab ab' (fun j => lp (us')[j] (List.getElem_mem _))
  let t := wordNativeMap F v (o'.perm.nodup hL') (ba ∘ (r).symm) (ba' ∘ (s).symm)
    (fun j => rpRead (vs')[j] (List.getElem_mem _))
  let E := wordEquiv o.perm hL
  let E' := wordEquiv o'.perm hL'
  let α : ∀ z, ab z ≅ (ba ∘ (r).symm) z := c.coefficient
  let β : ∀ z, ab' z ≅ (ba' ∘ (s).symm) z := d.coefficient
  let re := nativeReindex (A:=wordFamily ab us) (B:=wordFamily (ba ∘ (r).symm) vs) E (wordComparisonCells ab (ba ∘ (r).symm) o hL α)
  let re' := nativeReindex (A:=wordFamily ab' us') (B:=wordFamily (ba' ∘ (s).symm) vs') E' (wordComparisonCells ab' (ba' ∘ (s).symm) o' hL' β)
  have h : l.comp re' = re.comp t := by
    apply (wordNativeMap_square_iff (f:=F) ab (ba ∘ (r).symm) ab' (ba' ∘ (s).symm)
      o o' hL hL' hfl v α β lp rpRead).mpr
    intro i
    exact independentSwap_selected_cell R L P Q N ι f g A B A' B' p q hx hy o
      (vs')[i] (o'.perm.mem_iff.mpr (List.getElem_mem _)) (List.getElem_mem _)
  have H₀ : HEq originalL l :=
    wordProductMap_original_heq R L f g A B A' B' p q hf hg hx' hy'
  have H₁ : HEq originalR t :=
    (wordProductMap_original_heq R L g f B A B' A' q p hg hf hy' hx').trans
      (retagWordMap_heq r s G F (fun _ => rfl) rfl rfl (ba ∘ (r).symm) (ba' ∘ (s).symm)
        rp hfr hR' (o'.perm.nodup hL'))
  have e₀ := independentFamily_word (T:=T) A B xs ys
  have e₁ := independentFamily_word (T:=T) A' B' xs' ys'
  have e₂ : independentFamily T (wordFamily B ys) (wordFamily A xs) = wordFamily (ba ∘ (r).symm) vs := by
    rw [independentFamily_word]
    exact (wordFamily_read_eq ba (r).symm vs (ys.product xs) (equiv_word_read (r).symm _)).symm
  have e₃ : independentFamily T (wordFamily B' ys') (wordFamily A' xs') = wordFamily (ba' ∘ (s).symm) vs' := by
    rw [independentFamily_word]
    exact (wordFamily_read_eq ba' (s).symm vs' (ys'.product xs') (equiv_word_read (s).symm _)).symm
  have k₀ : HEq (swapX).hom.native re := by
    unfold independentSwapIso
    refine (NativeAugmentedIso.retarget_native_heq _ _ _).trans ?_
    unfold WordAugReadComparison.toIso
    exact NativeAugmentedIso.retarget_native_heq _ _ _
  have k₁ : HEq (swapY).hom.native re' := by
    unfold independentSwapIso
    refine (NativeAugmentedIso.retarget_native_heq _ _ _).trans ?_
    unfold WordAugReadComparison.toIso
    exact NativeAugmentedIso.retarget_native_heq _ _ _
  exact eq_of_heq ((nativeHom_comp_heq originalL (swapY).hom.native l re' e₀ e₁ e₃ H₀ k₁).trans
    ((heq_of_eq h).trans (nativeHom_comp_heq (swapX).hom.native originalR re t e₀ e₂ e₃ k₀ H₁).symm))

variable (NR : GatherOuterNat R) (NL : GatherLeftNat L)
variable [lF : ∀ c : C, (leftFactor T c).LaxBraided] [rF : ∀ c : C, (rightFactor (T:=T) c).LaxBraided]
variable (hl : ∀ c : C, SameLeftGather T c L) (hr : ∀ c : C, SameRightGather R c)
variable (xp : (wordNativeMap f hf hx' A A' (fun j => p xs'[j] (List.getElem_mem _))).comp (wordAug A' xs' bx).ε = (wordAug A xs ax).ε)
variable (yp : (wordNativeMap g hg hy' B B' (fun j => q ys'[j] (List.getElem_mem _))).comp (wordAug B' ys' by').ε = (wordAug B ys ay).ε)
set_option quotPrecheck false in
local notation "Pₐ" => (⟨pNative,xp⟩ : AugHom ℙ (wordAug A xs ax) (wordAug A' xs' bx))
set_option quotPrecheck false in
local notation "Qₐ" => (⟨qNative,yp⟩ : AugHom ℙ (wordAug B ys ay) (wordAug B' ys' by'))
local notation "indMap" => independentAugMap R L (J.ρ I) N NR NL hl hr

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2600000 in
/-- The original augmented independent swap is natural for arbitrary
carrier maps, with the original whole cell at each selected address. -/
theorem independentSwap_original_augmented_square :
    (indMap Pₐ Qₐ).comp (swapY).hom = (swapX).hom.comp (indMap Qₐ Pₐ) := by
  apply AugHom.ext
  exact independentSwap_original_native_square R L P Q N ι f g A B A' B' p q hf hg hx hy hx' hy'
    J swap_unit ax ay bx by'

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
