module
public import ContextualComposition.NativeDependentUnitWhisker
@[expose] public section

/-! Actual unit triangle for dependent accumulation: the middle
unit is a genuine singleton, not its empty-family neighbour. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [cat : Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)

def MulTriangle {T S : Bi (coeff (C:=C))} {I Z : C}
    (R : Gather S T Z) (J : UnitCompat R I) (P : TensorPrimitive T) : Prop :=
  ∀ a b, P.assoc a I b ≫ T.map (𝟙 a) (depLeftUnitCell R J P b) = T.map (J.ρ a) (𝟙 b)

set_option backward.isDefEq.respectTransparency false in
omit [MonoidalCategory C] [SymmetricCategory C] in
set_option linter.style.haveILetI false in
theorem standardMulTriangle (mul : MonoidalCategory C) (br : @BraidedCategory C cat mul)
    {S : Bi (coeff (C:=C))} {Z : C}
    (r : Gather S (binary (@Binary.ofMonoidal C cat mul)) Z)
    (j : UnitCompat r (@MonoidalCategoryStruct.tensorUnit C cat mul.toMonoidalCategoryStruct))
    (h : ∀ a : C, j.ρ a = (@MonoidalCategoryStruct.rightUnitor C cat mul.toMonoidalCategoryStruct a).hom) :
    MulTriangle r j (@tensorPrimitives C cat mul br) := by
  intro a b
  rw [standardDepLeftUnitCell mul br r j h, h a]
  letI := mul
  change (α_ a (𝟙_ C) b).hom ≫ (𝟙 a ⊗ₘ (λ_ b).hom) = (ρ_ a).hom ⊗ₘ 𝟙 b
  rw [id_tensorHom, tensorHom_id]
  exact triangle a b

section Actual
variable {X Y : Type u} {T : Bi (coeff (C:=C))} {I : C}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (J : UnitCompat R I) (P : TensorPrimitive T)
variable (NL : GatherLeftNat L) (Q : PrimitiveLinearity R L P) (U : AssocRightUnit R J P)
variable [lF : ∀ a : C, (leftFactor T a).LaxBraided]
variable (hl : ∀ a : C, SameLeftGather T a L) (ι : ∀ a b c, IsIso (P.assoc a b c))
variable (xs : List X) (ys : X → List Y) (A : X → C) (B : X → Y → C)
variable (a : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) A xs ⟶ I)
variable (b : ∀ x, fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) (B x) (ys x) ⟶ I)
set_option quotPrecheck false in
local notation "oneW" => (fun _ : X => ([PUnit.unit] : List PUnit))
set_option quotPrecheck false in
local notation "oneL" => (fun (_ : X) (_ : PUnit) => I)
set_option quotPrecheck false in
local notation "oneA" => (fun _ : X => (ρ_ I).hom)
set_option quotPrecheck false in
local notation "nextW" => (fun x (_ : PUnit) => ys x)
set_option quotPrecheck false in
local notation "nextL" => (fun x (_ : PUnit) => B x)
set_option quotPrecheck false in
local notation "nextA" => (fun x (_ : PUnit) => b x)
set_option quotPrecheck false in
local notation "leftW" => dependentWord (dependentWord xs oneW) (fun p => ys (Prod.fst p))
set_option quotPrecheck false in
local notation "rightW" => dependentWord xs (fun x => dependentWord (oneW x) (nextW x))

set_option backward.isDefEq.respectTransparency false in
noncomputable def triangleAssoc (hn : (rightW).Nodup) :=
  dependentAssocIso R L J P NL Q U xs oneW nextW A oneL nextL a oneA nextA hl ι hn

theorem triangleReadParent :
    (dependentWord xs oneW).map Prod.fst = xs := by
  change (xs.flatMap (fun x => [(x,PUnit.unit)])).map Prod.fst = xs
  rw [flatMap_single_eq_map, List.map_map]
  exact List.map_id xs

theorem triangleReadChild (x : X) :
    (dependentWord (oneW x) (nextW x)).map Prod.snd = ys x := by
  change (((ys x).map (Prod.mk PUnit.unit)) ++ []).map Prod.snd = ys x
  rw [List.append_nil, List.map_map]
  exact List.map_id _

set_option backward.isDefEq.respectTransparency false in
noncomputable def triangleDropParent
    (iρ : ∀ c, IsIso (J.ρ c)) (hn : (leftW).Nodup) :
    NativeAugmentedIso
      (dependentAssocLeft R L J xs oneW nextW A oneL nextL a oneA nextA)
      (dependentWordAug R L J xs ys A B (indexedAugmentation b) a) := by
  let p (t : X × PUnit.{u+1}) : T.obj (A t.1) I ≅ A t.1 := by
    let _ := iρ (A t.1)
    exact asIso (J.ρ (A t.1))
  let v := dependentWordAugCell R L J xs oneW A oneL (indexedAugmentation oneA) a
  have hη : indexedAugmentation (B:=oneL) (us:=oneW) oneA = oneA := by
    funext x
    change eqToHom _ ≫ (ρ_ I).hom = (ρ_ I).hom
    simp
  have hv : wordAug (dependentLabels (T:=T) A oneL) (dependentWord xs oneW) v =
      wordAug (fun x => T.obj (A x) I) xs (act 𝒮 Zₐ (fun x => J.ρ (A x)) xs ≫ a) := by
    change dependentWordAug R L J xs oneW A oneL (indexedAugmentation oneA) a = _
    rw [hη]
    exact dependentWordAug_rightUnit_chart R L J xs A a (fun x => hl (A x))
  exact dependentParentWhiskerIso R L J NL Prod.fst
    (dependentWord xs oneW) xs (triangleReadParent xs) ys p v a b
    (wordAug_act_preserves_pullback Prod.fst _ xs (triangleReadParent xs)
      (fun x => J.ρ (A x)) v a hv) hn

set_option backward.isDefEq.respectTransparency false in
noncomputable def triangleDropChild
    (hI : depLeftUnitCell R J P I = J.ρ I) (iLeft : ∀ c, IsIso (depLeftUnitCell R J P c))
    (hn : (rightW).Nodup) :
    NativeAugmentedIso
      (dependentAssocRight R L J xs oneW nextW A oneL nextL a oneA nextA)
      (dependentWordAug R L J xs ys A B (indexedAugmentation b) a) := by
  let q (x : X) (t : PUnit.{u+1} × Y) : T.obj I (B x t.2) ≅ B x t.2 := by
    let _ := iLeft (B x t.2)
    exact asIso (depLeftUnitCell R J P (B x t.2))
  let v (x : X) := dependentWordAugCell R L J (oneW x) (nextW x) (oneL x) (nextL x)
    (indexedAugmentation (nextA x)) (oneA x)
  exact dependentChildWhiskerIso R L J NL (fun _ => Prod.snd) xs
    (fun x => dependentWord (oneW x) (nextW x)) ys (triangleReadChild ys) q a v b
    (fun x => wordAug_act_preserves_pullback Prod.snd _ (ys x) (triangleReadChild ys x)
      (fun y => depLeftUnitCell R J P (B x y)) (v x) (b x)
      (dependentWordAug_leftUnit_chart R L J P Q (ys x) (B x) (b x) hI)) hn


theorem triangleLeft_read :
    (leftW).map (fun t => (t.1.1,t.2)) = dependentWord xs ys := by
  simp only [dependentWord, List.map_flatMap, List.flatMap_map, List.map_map, List.flatMap_assoc]
  simp
  rfl

theorem triangleRight_read :
    (rightW).map (fun t => (t.1,t.2.2)) = dependentWord xs ys := by
  simp only [dependentWord, List.map_flatMap, List.map_map]
  simp
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3500000 in
/-- The actual augmented native triangle, with all three edges
constructed on the original dependent augmentations. -/
theorem actual_dependent_augmented_triangle
    (hI : depLeftUnitCell R J P I = J.ρ I) (iLeft : ∀ c, IsIso (depLeftUnitCell R J P c))
    (iρ : ∀ c, IsIso (J.ρ c)) (hL : (leftW).Nodup) (hR : (rightW).Nodup)
    (h : MulTriangle R J P) :
    (triangleAssoc R L J P NL Q U hl ι xs ys A B a b hR).hom.comp
      (triangleDropChild R L J P NL Q xs ys A B a b hI iLeft hR).hom =
    (triangleDropParent R L J NL hl xs ys A B a b iρ hL).hom := by
  let p := (triangleAssoc R L J P NL Q U hl ι xs ys A B a b hR).hom
  let q := (triangleDropChild R L J P NL Q xs ys A B a b hI iLeft hR).hom
  let r := (triangleDropParent R L J NL hl xs ys A B a b iρ hL).hom
  let t := dependentWord xs ys
  let g : (X × PUnit.{u+1}) × Y → X × Y := fun k => (k.1.1,k.2)
  let f : X × PUnit.{u+1} × Y → X × Y := fun k => (k.1,k.2.2)
  let A₀ (k : X × Y) := T.obj (T.obj (A k.1) I) (B k.1 k.2)
  let A₁ (k : X × Y) := T.obj (A k.1) (T.obj I (B k.1 k.2))
  let A₂ (k : X × Y) := T.obj (A k.1) (B k.1 k.2)
  let p₀ (k) : A₀ k ⟶ A₁ k := P.assoc (A k.1) I (B k.1 k.2)
  let q₀ (k) : A₁ k ⟶ A₂ k := T.map (𝟙 (A k.1)) (depLeftUnitCell R J P (B k.1 k.2))
  let r₀ (k) : A₀ k ⟶ A₂ k := T.map (J.ρ (A k.1)) (𝟙 (B k.1 k.2))
  have hf : (rightW).map f = t := triangleRight_read xs ys
  have hg : (leftW).map g = t := triangleLeft_read xs ys
  have h₀ : (dependentAssocLeft R L J xs oneW nextW A oneL nextL a oneA nextA).base = wordFamily A₀ t :=
    wordFamily_read_eq A₀ g leftW t hg
  have h₁ : (dependentAssocRight R L J xs oneW nextW A oneL nextL a oneA nextA).base = wordFamily A₁ t :=
    wordFamily_read_eq A₁ f rightW t hf
  have hp : HEq p.native (wordPointwise rightW (fun z => p₀ (f z))) := by
    unfold p triangleAssoc
    exact dependentAssocIso_pointwise_heq R L J P NL Q U hl _ _ _ _ _ _ _ _ _ ι hR
  have hq : HEq q.native (wordPointwise rightW (fun z => q₀ (f z))) := by
    unfold q triangleDropChild
    dsimp only
    exact dependentChildWhiskerIso_pointwise R L J NL _ _ _ _ _ _ _ _ _ _ _
  have hr : HEq r.native (wordPointwise leftW (fun z => r₀ (g z))) := by
    unfold r triangleDropParent
    dsimp only
    exact dependentParentWhiskerIso_pointwise R L J NL _ _ _ _ _ _ _ _ _ _ _
  have k : (wordPointwise t p₀).comp (wordPointwise t q₀) = wordPointwise t r₀ :=
    (wordPointwise_comp t p₀ q₀).trans (wordPointwise_eq_of_mem t _ _ (fun k _ => h (A k.1) (B k.1 k.2)))
  apply AugHom.ext
  change p.native.comp q.native = r.native
  exact eq_of_heq ((nativeHom_comp_heq p.native q.native _ _ h₀ h₁ rfl
    (hp.trans (wordPointwise_retag_heq f rightW t hf p₀))
    (hq.trans (wordPointwise_retag_heq f rightW t hf q₀))).trans
    ((heq_of_eq k).trans (hr.trans (wordPointwise_retag_heq g leftW t hg r₀)).symm))

end Actual

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
