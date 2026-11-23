module
public import ContextualComposition.NativeDependentStructuralRead
@[expose] public section

/-! The original whole dependent augmentations on either side of a
parent or child raw read are used as actual whiskering endpoints. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)

variable {X X' Y Y' : Type u} {T : Bi (coeff (C:=C))} {I : C}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (J : UnitCompat R I)

set_option backward.isDefEq.respectTransparency false in
theorem dependentAug_parent_read {V : X' → C} {W : X' → Y → C}
    (g : X → X') (xs : List X) (xs' : List X') (h : xs.map g = xs') (ys : X' → List Y)
    (ε : fold 𝒮 Zₐ V xs' ⟶ I) (δ : ∀ x, fold 𝒮 Zₐ (W x) (ys x) ⟶ I) :
    let e := (std_fold_map V g xs).symm.trans (congrArg (fold 𝒮 Zₐ V) h)
    dependentWordAug R L J xs (ys ∘ g) (V ∘ g) (W ∘ g)
        (indexedAugmentation (fun x => δ (g x))) (eqToHom e ≫ ε) =
      dependentWordAug R L J xs' ys V W (indexedAugmentation δ) ε := by
  intro e
  let f := fun z : X × Y => (g z.1,z.2)
  have k : (dependentWord xs (ys ∘ g)).map f = dependentWord xs' ys := by
    subst xs'
    simp only [dependentWord, List.map_flatMap, List.flatMap_map, List.map_map]
    rfl
  exact wordAug_read_eq (dependentLabels (T:=T) V W) f _ _ k _ _
    (dependentAug_parent_retag R L J xs xs' ys V W g h ε δ)

set_option backward.isDefEq.respectTransparency false in
theorem dependentAug_child_read {V : X → C} {W : X → Y' → C}
    (g : X → Y → Y') (xs : List X) (ys : X → List Y) (ys' : X → List Y')
    (h : ∀ x, (ys x).map (g x) = ys' x)
    (ε : fold 𝒮 Zₐ V xs ⟶ I) (δ : ∀ x, fold 𝒮 Zₐ (W x) (ys' x) ⟶ I) :
    let e := fun x => (std_fold_map (W x) (g x) (ys x)).symm.trans
      (congrArg (fold 𝒮 Zₐ (W x)) (h x))
    dependentWordAug R L J xs ys V (fun x => W x ∘ g x)
        (indexedAugmentation (fun x => eqToHom (e x) ≫ δ x)) ε =
      dependentWordAug R L J xs ys' V W (indexedAugmentation δ) ε := by
  intro e
  let f := fun z : X × Y => (z.1,g z.1 z.2)
  have k : (dependentWord xs ys).map f = dependentWord xs ys' := by
    simp only [dependentWord, List.map_flatMap]
    apply congrArg (fun a => xs.flatMap a)
    funext x
    rw [← h x, List.map_map, List.map_map]
    rfl
  exact wordAug_read_eq (dependentLabels (T:=T) V W) f _ _ k _ _
    (dependentAug_child_retag R L J xs ys ys' V W g h ε δ)


section Whisker
variable (NL : GatherLeftNat L)

set_option backward.isDefEq.respectTransparency false in
noncomputable def dependentParentWhiskerIso
    {V : X → C} {V' : X' → C} {W : X' → Y → C}
    (g : X → X') (xs : List X) (xs' : List X') (h : xs.map g = xs') (ys : X' → List Y)
    (p : ∀ x, V x ≅ V' (g x)) (ε : fold 𝒮 Zₐ V xs ⟶ I)
    (ε' : fold 𝒮 Zₐ V' xs' ⟶ I) (δ : ∀ x, fold 𝒮 Zₐ (W x) (ys x) ⟶ I)
    (hp : act 𝒮 Zₐ (fun x => (p x).hom) xs ≫
      eqToHom ((std_fold_map V' g xs).symm.trans (congrArg (fold 𝒮 Zₐ V') h)) ≫ ε' = ε)
    (hn : (dependentWord xs (ys ∘ g)).Nodup) :
    NativeAugmentedIso
      (dependentWordAug R L J xs (ys ∘ g) V (W ∘ g) (indexedAugmentation (fun x => δ (g x))) ε)
      (dependentWordAug R L J xs' ys V' W (indexedAugmentation δ) ε') := by
  let e := (std_fold_map V' g xs).symm.trans (congrArg (fold 𝒮 Zₐ V') h)
  let q := fun x y => Iso.refl (W (g x) y)
  have hq (x : X) : act 𝒮 Zₐ (fun y => (q x y).hom) (ys (g x)) ≫ δ (g x) = δ (g x) := by
    have e₀ : act 𝒮 Zₐ (fun y => 𝟙 (W (g x) y)) (ys (g x)) = 𝟙 _ := act_id_grid _
    rw [show (fun y => (q x y).hom) = (fun y => 𝟙 (W (g x) y)) from rfl, e₀]
    exact Category.id_comp _
  have hp' : act 𝒮 Zₐ (fun x => (p x).hom) xs ≫ (eqToHom e ≫ ε') = ε := hp
  exact (dependentWhiskerIso R L J NL xs (ys ∘ g) p q ε (eqToHom e ≫ ε')
    (fun x => δ (g x)) (fun x => δ (g x)) hp' hq hn).retarget rfl
    (dependentAug_parent_read R L J g xs xs' h ys ε' δ)

set_option backward.isDefEq.respectTransparency false in
noncomputable def dependentChildWhiskerIso
    {V : X → C} {W : X → Y → C} {W' : X → Y' → C}
    (g : X → Y → Y') (xs : List X) (ys : X → List Y) (ys' : X → List Y')
    (h : ∀ x, (ys x).map (g x) = ys' x)
    (q : ∀ x y, W x y ≅ W' x (g x y)) (ε : fold 𝒮 Zₐ V xs ⟶ I)
    (δ : ∀ x, fold 𝒮 Zₐ (W x) (ys x) ⟶ I) (δ' : ∀ x, fold 𝒮 Zₐ (W' x) (ys' x) ⟶ I)
    (hq : ∀ x, act 𝒮 Zₐ (fun y => (q x y).hom) (ys x) ≫
      eqToHom ((std_fold_map (W' x) (g x) (ys x)).symm.trans (congrArg (fold 𝒮 Zₐ (W' x)) (h x))) ≫
        δ' x = δ x)
    (hn : (dependentWord xs ys).Nodup) :
    NativeAugmentedIso
      (dependentWordAug R L J xs ys V W (indexedAugmentation δ) ε)
      (dependentWordAug R L J xs ys' V W' (indexedAugmentation δ') ε) := by
  let e := fun x => (std_fold_map (W' x) (g x) (ys x)).symm.trans (congrArg (fold 𝒮 Zₐ (W' x)) (h x))
  let p := fun x => Iso.refl (V x)
  have hp : act 𝒮 Zₐ (fun x => (p x).hom) xs ≫ ε = ε := by
    have e₀ : act 𝒮 Zₐ (fun x => 𝟙 (V x)) xs = 𝟙 _ := act_id_grid _
    rw [show (fun x => (p x).hom) = (fun x => 𝟙 (V x)) from rfl, e₀]
    exact Category.id_comp _
  have hq' (x : X) : act 𝒮 Zₐ (fun y => (q x y).hom) (ys x) ≫ (eqToHom (e x) ≫ δ' x) = δ x := hq x
  exact (dependentWhiskerIso R L J NL xs ys p q ε ε δ (fun x => eqToHom (e x) ≫ δ' x) hp hq' hn).retarget rfl
    (dependentAug_child_read R L J g xs ys ys' h ε δ')

set_option backward.isDefEq.respectTransparency false in
theorem dependentParentWhiskerIso_pointwise
    {V : X → C} {V' : X' → C} {W : X' → Y → C}
    (g : X → X') (xs : List X) (xs' : List X') (h : xs.map g = xs') (ys : X' → List Y)
    (p : ∀ x, V x ≅ V' (g x)) (ε : fold 𝒮 Zₐ V xs ⟶ I)
    (ε' : fold 𝒮 Zₐ V' xs' ⟶ I) (δ : ∀ x, fold 𝒮 Zₐ (W x) (ys x) ⟶ I)
    (hp : act 𝒮 Zₐ (fun x => (p x).hom) xs ≫
      eqToHom ((std_fold_map V' g xs).symm.trans (congrArg (fold 𝒮 Zₐ V') h)) ≫ ε' = ε)
    (hn : (dependentWord xs (ys ∘ g)).Nodup) :
    HEq (dependentParentWhiskerIso R L J NL g xs xs' h ys p ε ε' δ hp hn).hom.native
      (wordPointwise (dependentWord xs (ys ∘ g)) (fun z => T.map (p z.1).hom (𝟙 (W (g z.1) z.2)))) := by
  unfold dependentParentWhiskerIso
  dsimp only
  exact (NativeAugmentedIso.retarget_native_heq _ _ _).trans
    (heq_of_eq (dependentWhiskerIso_native _ _ _ _ _ _ _ _ _ _ _ _ _ _ _))

set_option backward.isDefEq.respectTransparency false in
theorem dependentChildWhiskerIso_pointwise
    {V : X → C} {W : X → Y → C} {W' : X → Y' → C}
    (g : X → Y → Y') (xs : List X) (ys : X → List Y) (ys' : X → List Y')
    (h : ∀ x, (ys x).map (g x) = ys' x)
    (q : ∀ x y, W x y ≅ W' x (g x y)) (ε : fold 𝒮 Zₐ V xs ⟶ I)
    (δ : ∀ x, fold 𝒮 Zₐ (W x) (ys x) ⟶ I) (δ' : ∀ x, fold 𝒮 Zₐ (W' x) (ys' x) ⟶ I)
    (hq : ∀ x, act 𝒮 Zₐ (fun y => (q x y).hom) (ys x) ≫
      eqToHom ((std_fold_map (W' x) (g x) (ys x)).symm.trans (congrArg (fold 𝒮 Zₐ (W' x)) (h x))) ≫
        δ' x = δ x)
    (hn : (dependentWord xs ys).Nodup) :
    HEq (dependentChildWhiskerIso R L J NL g xs ys ys' h q ε δ δ' hq hn).hom.native
      (wordPointwise (dependentWord xs ys) (fun z => T.map (𝟙 (V z.1)) (q z.1 z.2).hom)) := by
  unfold dependentChildWhiskerIso
  dsimp only
  exact (NativeAugmentedIso.retarget_native_heq _ _ _).trans
    (heq_of_eq (dependentWhiskerIso_native _ _ _ _ _ _ _ _ _ _ _ _ _ _ _))

end Whisker

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
