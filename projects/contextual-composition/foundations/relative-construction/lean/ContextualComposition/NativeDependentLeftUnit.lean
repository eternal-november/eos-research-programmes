module
public import ContextualComposition.NativeDependentFourLevel
@[expose] public section

/-! The left unit is supplied by the same distributivity and right-unit
data, using multiplicative braiding to derive its left distribution law. -/
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
variable (J : UnitCompat R I) (P : TensorPrimitive T) (Q : PrimitiveLinearity R L P)

def depLeftUnitCell {S : Bi (coeff (C:=C))} {Z : C}
    (r : Gather S T Z) (j : UnitCompat r I) (p : TensorPrimitive T) (a : C) : T.obj I a ⟶ a :=
  p.swap I a ≫ j.ρ a

set_option backward.isDefEq.respectTransparency false in
theorem depLeftUnitCell_natural {a b : C} (p : a ⟶ b) :
    T.map (𝟙 I) p ≫ depLeftUnitCell R J P b = depLeftUnitCell R J P a ≫ p := by
  unfold depLeftUnitCell
  have hp : T.map (𝟙 I) p ≫ P.swap I b = P.swap I a ≫ T.map p (𝟙 I) := P.swap_nat (𝟙 I) p
  have hq : T.map p (𝟙 I) ≫ J.ρ b = J.ρ a ≫ p := J.natural p
  rw [reassoc_of% hp, hq, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
include Q in
theorem depLeftUnit_collect {X : Type u} (A : X → C) (xs : List X) :
    (Lin.left L I).collect A xs ≫ depLeftUnitCell R J P (fold 𝒮 Zₐ A xs) =
      act 𝒮 Zₐ (fun x => depLeftUnitCell R J P (A x)) xs := by
  let p := fun x => P.swap I (A x)
  let q := fun x => J.ρ (A x)
  have h : (Lin.left L I).collect A xs ≫ P.swap I (fold 𝒮 Zₐ A xs) =
      act 𝒮 Zₐ p xs ≫ (Lin.right R I).collect A xs := (Q.sl I).collect A xs
  have k : (Lin.right R I).collect A xs ≫ J.ρ (fold 𝒮 Zₐ A xs) = act 𝒮 Zₐ q xs := by
    rw [collect_right_eq]
    exact gather_unit J A xs
  unfold depLeftUnitCell
  rw [← Category.assoc, h, Category.assoc, k]
  exact act_seq 𝒮 Zₐ p q xs


set_option backward.isDefEq.respectTransparency false in
include Q in
theorem dependentWordAug_leftUnit_chart {X : Type u}
    (xs : List X) (A : X → C) (ε : fold 𝒮 Zₐ A xs ⟶ I)
    (hI : depLeftUnitCell R J P I = J.ρ I) :
    dependentWordAug R L J ([PUnit.unit] : List PUnit.{u+1}) (fun _ => xs)
      (fun _ => I) (fun _ => A) (indexedAugmentation (fun _ => ε)) (ρ_ I).hom =
    wordAug (fun x => T.obj I (A x)) xs (act 𝒮 Zₐ (fun x => depLeftUnitCell R J P (A x)) xs ≫ ε) := by
  let s : X → PUnit.{u+1} × X := fun x => (PUnit.unit,x)
  let B := fun x => T.obj I (A x)
  let D := B ∘ (Prod.snd : PUnit.{u+1} × X → X)
  let us := ([PUnit.unit] : List PUnit.{u+1})
  let w := dependentWord us (fun _ => xs)
  let q := fun x => depLeftUnitCell R J P (A x)
  let p := dependentWordAugCell R L J us (fun _ => xs) (fun _ => I) (fun _ => A)
    (indexedAugmentation (fun _ => ε)) (ρ_ I).hom
  have hread : w.map Prod.snd = xs := by
    change ((xs.map s) ++ []).map Prod.snd = xs
    rw [List.append_nil, List.map_map]
    exact List.map_id xs
  change wordAug D w p = wordAug B xs (act 𝒮 Zₐ q xs ≫ ε)
  apply wordAug_read_eq B Prod.snd w xs hread
  let e₀ := std_fold_map D s xs
  let e₁ := congrArg (fold 𝒮 Zₐ D) (List.append_nil (xs.map s)).symm
  let e := e₀.symm.trans e₁
  suffices key : eqToHom e ≫ p = act 𝒮 Zₐ q xs ≫ ε by
    exact (hom_source_pin_heq e p).symm.trans (heq_of_eq key)
  let F := fold 𝒮 Zₐ D (xs.map s)
  let N := fold 𝒮 Zₐ B xs
  let r : N ⟶ I := (Lin.left L I).collect A xs ≫ T.map (𝟙 I) ε ≫ J.ρ I
  let k : F ⟶ N := eqToHom e₀
  have hr : r = act 𝒮 Zₐ q xs ≫ ε := by
    unfold r
    rw [← hI, depLeftUnitCell_natural R J P ε,
      ← Category.assoc, depLeftUnit_collect R L J P Q]
  have hx := dependentWordAug_raw_rows R L J us (fun _ => xs) (fun _ => I) (fun _ => A)
    (fun _ => ε) (ρ_ I).hom
  change p = taggedRaggedRows D Prod.mk (fun _ => xs) us ≫ act 𝒮 Zₐ (fun _ => r) us ≫ (ρ_ I).hom at hx
  unfold taggedRaggedRows at hx
  simp only [Category.assoc] at hx
  change p = (rowsChart D (fun z : PUnit.{u+1} => xs.map (Prod.mk z)) us ≫
      ((k ⊗ₘ 𝟙 (𝟙_ C)) ≫ ((r ⊗ₘ 𝟙 (𝟙_ C)) ≫ (ρ_ I).hom))) at hx
  have hk : (k ⊗ₘ 𝟙 (𝟙_ C)) ≫ (ρ_ N).hom = (ρ_ F).hom ≫ k := by
    rw [tensorHom_id]
    exact rightUnitor_naturality k
  have hh : (r ⊗ₘ 𝟙 (𝟙_ C)) ≫ (ρ_ I).hom = (ρ_ N).hom ≫ r := by
    rw [tensorHom_id]
    exact rightUnitor_naturality r
  have hu := rowsChart_one D (fun z : PUnit.{u+1} => xs.map (Prod.mk z)) PUnit.unit
  change eqToHom e₁ ≫ rowsChart D (fun z : PUnit.{u+1} => xs.map (Prod.mk z)) us ≫ (ρ_ F).hom =
    𝟙 F at hu
  rw [hx, hh, reassoc_of% hk]
  change eqToHom (e₀.symm.trans e₁) ≫ _ = _
  rw [← eqToHom_trans e₀.symm e₁]
  simp only [Category.assoc]
  rw [reassoc_of% hu, Category.id_comp]
  change eqToHom e₀.symm ≫ eqToHom e₀ ≫ r = _
  rw [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  exact hr


set_option backward.isDefEq.respectTransparency false in
noncomputable def dependentLeftUnitIso {X : Type u}
    (xs : List X) (A : X → C) (ε : fold 𝒮 Zₐ A xs ⟶ I)
    (hI : depLeftUnitCell R J P I = J.ρ I) (ι : ∀ a, IsIso (depLeftUnitCell R J P a))
    (hn : xs.Nodup) :
    NativeAugmentedIso
      (dependentWordAug R L J ([PUnit.unit] : List PUnit.{u+1}) (fun _ => xs)
        (fun _ => I) (fun _ => A) (indexedAugmentation (fun _ => ε)) (ρ_ I).hom)
      (wordAug A xs ε) := by
  let B := fun x => T.obj I (A x)
  let φ (x : X) : B x ≅ A x := by
    let _ := ι (A x)
    exact asIso (depLeftUnitCell R J P (A x))
  let p := act 𝒮 Zₐ (fun x => depLeftUnitCell R J P (A x)) xs ≫ ε
  have hp : AddressOrder.mapSum additiveStructure B (.ident xs) ≫
      act 𝒮 Zₐ (fun x => (φ x).hom) xs ≫ ε = p := by
    change 𝟙 _ ≫ p = p
    exact Category.id_comp _
  exact (wordAugIso B A (.ident xs) hn φ p ε hp).retarget
    (dependentWordAug_leftUnit_chart R L J P Q xs A ε hI).symm rfl

set_option backward.isDefEq.respectTransparency false in
omit [MonoidalCategory C] [SymmetricCategory C] in
set_option linter.style.haveILetI false in
theorem standardDepLeftUnitCell (mul : MonoidalCategory C) (br : @BraidedCategory C cat mul)
    {S : Bi (coeff (C:=C))} {Z : C}
    (r : Gather S (binary (@Binary.ofMonoidal C cat mul)) Z)
    (j : UnitCompat r (@MonoidalCategoryStruct.tensorUnit C cat mul.toMonoidalCategoryStruct))
    (h : ∀ a : C, j.ρ a = (@MonoidalCategoryStruct.rightUnitor C cat mul.toMonoidalCategoryStruct a).hom)
    (a : C) :
    depLeftUnitCell r j (@tensorPrimitives C cat mul br) a =
      (@MonoidalCategoryStruct.leftUnitor C cat mul.toMonoidalCategoryStruct a).hom := by
  unfold depLeftUnitCell
  rw [h]
  letI := mul
  letI := br
  change (β_ (𝟙_ C) a).hom ≫ (ρ_ a).hom = (λ_ a).hom
  exact braiding_rightUnitor a

set_option backward.isDefEq.respectTransparency false in
omit [MonoidalCategory C] [SymmetricCategory C] in
set_option linter.style.haveILetI false in
theorem standardDepLeftUnit_agrees_at_unit (mul : MonoidalCategory C) (br : @BraidedCategory C cat mul)
    {S : Bi (coeff (C:=C))} {Z : C}
    (r : Gather S (binary (@Binary.ofMonoidal C cat mul)) Z)
    (j : UnitCompat r (@MonoidalCategoryStruct.tensorUnit C cat mul.toMonoidalCategoryStruct))
    (h : ∀ a : C, j.ρ a = (@MonoidalCategoryStruct.rightUnitor C cat mul.toMonoidalCategoryStruct a).hom) :
    depLeftUnitCell r j (@tensorPrimitives C cat mul br)
      (@MonoidalCategoryStruct.tensorUnit C cat mul.toMonoidalCategoryStruct) = j.ρ _ := by
  rw [standardDepLeftUnitCell mul br r j h, h]
  letI := mul
  monoidal_coherence

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
