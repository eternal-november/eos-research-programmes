module
public import ContextualComposition.NativeFubiniRegroup
@[expose] public section

/-! Actual dependent augmentation transport under parent and
continuation permutations. Every whole cell, including a nullary one,
is transported by the exact ordered fold change. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)

variable {X Y : Type u} {T : Bi (coeff (C:=C))} {I : C}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (J : UnitCompat R I)
variable (V : X → C) (W : X → Y → C)

set_option backward.isDefEq.respectTransparency false in
theorem dependentAug_parent_order {xs xs' : List X} (ys : X → List Y) (p : AddressOrder X xs xs')
    (ε : fold 𝒮 Zₐ V xs' ⟶ I) (δ : ∀ x, fold 𝒮 Zₐ (W x) (ys x) ⟶ I) :
    AddressOrder.mapSum additiveStructure (dependentLabels (T:=T) V W)
      (liftRows (fun x => (ys x).map (Prod.mk x)) p) ≫
    dependentWordAugCell R L J xs' ys V W (indexedAugmentation δ) ε =
      dependentWordAugCell R L J xs ys V W (indexedAugmentation δ)
        (AddressOrder.mapSum additiveStructure V p ≫ ε) := by
  let A := dependentLabels (T:=T) V W
  let f (x : X) : fold 𝒮 Zₐ (A ∘ Prod.mk x) (ys x) ⟶ V x :=
    (Lin.left L (V x)).collect (W x) (ys x) ≫ T.map (𝟙 (V x)) (δ x) ≫ J.ρ (V x)
  have a : dependentWordAugCell R L J xs' ys V W (indexedAugmentation δ) ε =
      taggedRaggedRows A Prod.mk ys xs' ≫ act 𝒮 Zₐ f xs' ≫ ε :=
    dependentWordAug_raw_rows R L J xs' ys V W δ ε
  have b : dependentWordAugCell R L J xs ys V W (indexedAugmentation δ)
        (AddressOrder.mapSum additiveStructure V p ≫ ε) =
      taggedRaggedRows A Prod.mk ys xs ≫ act 𝒮 Zₐ f xs ≫ AddressOrder.mapSum additiveStructure V p ≫ ε :=
    dependentWordAug_raw_rows R L J xs ys V W δ _
  have c := taggedRaggedRows_parent_order A V Prod.mk ys p f
  rw [a,b]
  simpa only [Category.assoc] using congrArg (fun t => t ≫ ε) c.symm

set_option backward.isDefEq.respectTransparency false in
theorem dependentAug_child_order (xs : List X) {ys ys' : X → List Y} (p : ∀ x, AddressOrder Y (ys x) (ys' x))
    (ε : fold 𝒮 Zₐ V xs ⟶ I) (δ : ∀ x, fold 𝒮 Zₐ (W x) (ys' x) ⟶ I)
    [lF : ∀ x, (leftFactor T (V x)).LaxBraided] (hl : ∀ x, SameLeftGather T (V x) L) :
    AddressOrder.mapSum additiveStructure (dependentLabels (T:=T) V W)
      (rowOrders (fun x => (p x).relabel (Prod.mk x)) xs) ≫
    dependentWordAugCell R L J xs ys' V W (indexedAugmentation δ) ε =
      dependentWordAugCell R L J xs ys V W
        (indexedAugmentation (fun x => AddressOrder.mapSum additiveStructure (W x) (p x) ≫ δ x)) ε := by
  let A := dependentLabels (T:=T) V W
  let a := fun x => AddressOrder.mapSum additiveStructure (W x) (p x)
  let b := fun x => AddressOrder.mapSum additiveStructure (A ∘ Prod.mk x) (p x)
  let d := fun x => (Lin.left L (V x)).collect (W x) (ys' x) ≫ T.map (𝟙 (V x)) (δ x) ≫ J.ρ (V x)
  let c := fun x => (Lin.left L (V x)).collect (W x) (ys x) ≫ T.map (𝟙 (V x)) (a x ≫ δ x) ≫ J.ρ (V x)
  have h (x : X) : b x ≫ d x = c x := by
    let F := leftFactor T (V x)
    have t : b x ≫ (Lin.left L (V x)).collect (W x) (ys' x) =
        (Lin.left L (V x)).collect (W x) (ys x) ≫ F.map (a x) := by
      have v := collect_order F (W x) (p x)
      simp only [F, leftFactor_sameCollect T (V x) L (hl x)] at v
      exact v
    change b x ≫ (Lin.left L (V x)).collect (W x) (ys' x) ≫ F.map (δ x) ≫ J.ρ (V x) =
      (Lin.left L (V x)).collect (W x) (ys x) ≫ F.map (a x ≫ δ x) ≫ J.ρ (V x)
    rw [reassoc_of% t, F.map_comp, Category.assoc]
  have k : act 𝒮 Zₐ b xs ≫ act 𝒮 Zₐ d xs = act 𝒮 Zₐ c xs :=
    (act_seq 𝒮 Zₐ b d xs).trans (congrArg (fun l => act 𝒮 Zₐ l xs) (funext h))
  have j := taggedRaggedRows_order A Prod.mk p xs
  have a₀ : dependentWordAugCell R L J xs ys' V W (indexedAugmentation δ) ε =
    taggedRaggedRows A Prod.mk ys' xs ≫ act 𝒮 Zₐ d xs ≫ ε :=
    dependentWordAug_raw_rows R L J xs ys' V W δ ε
  have a₁ : dependentWordAugCell R L J xs ys V W (indexedAugmentation (fun x => a x ≫ δ x)) ε =
    taggedRaggedRows A Prod.mk ys xs ≫ act 𝒮 Zₐ c xs ≫ ε :=
    dependentWordAug_raw_rows R L J xs ys V W (fun x => a x ≫ δ x) ε
  rw [a₀,a₁,reassoc_of% j,reassoc_of% k]

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
