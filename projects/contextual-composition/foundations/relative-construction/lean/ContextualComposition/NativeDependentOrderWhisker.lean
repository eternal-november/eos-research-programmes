module
public import ContextualComposition.NativeDependentOrder
@[expose] public section

/-! The exact permutation-aware structural whiskering rule. A change
in parent order and a change in child order have separate native
charts and separate whole-augmentation obligations. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)

set_option backward.isDefEq.respectTransparency false in
theorem wordReindex_preserves_iff {X : Type u} {I : C} (A B : X → C) {xs ys : List X}
    (p : AddressOrder X xs ys) (hx : xs.Nodup) (φ : ∀ x, A x ≅ B x)
    (a : fold 𝒮 Zₐ A xs ⟶ I) (b : fold 𝒮 Zₐ B ys ⟶ I) :
    (nativeReindex (wordEquiv p.perm hx) (wordComparisonCells A B p hx φ)).comp
        (wordAug B ys b).ε = (wordAug A xs a).ε ↔
      AddressOrder.mapSum additiveStructure A p ≫ act 𝒮 Zₐ (fun x => (φ x).hom) ys ≫ b = a := by
  constructor
  · intro h
    let c := AddressOrder.mapSum additiveStructure A p ≫ act 𝒮 Zₐ (fun x => (φ x).hom) ys ≫ b
    have h₀ := wordAug_preserving A B p hx φ c b rfl
    have hc : (wordAug A xs c).ε = (wordAug A xs a).ε := h₀.symm.trans h
    have hd : wordAug A xs c = wordAug A xs a := congrArg (Aug.mk (wordFamily A xs)) hc
    exact eq_of_heq (wordAug_cell_heq c a hd)
  · exact wordAug_preserving A B p hx φ a b

variable {X Y : Type u} {T : Bi (coeff (C:=C))} {I : C}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (J : UnitCompat R I) (NL : GatherLeftNat L)
variable {xs xs' : List X} {ys ys' : X → List Y}
variable {A A' : X → C} {B B' : X → Y → C}
variable (e : AddressOrder X xs xs') (d : ∀ x, AddressOrder Y (ys x) (ys' x))
variable (p : ∀ x, A x ≅ A' x) (q : ∀ x y, B x y ≅ B' x y)
variable (ε : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) A xs ⟶ I)
variable (ε' : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) A' xs' ⟶ I)
variable (δ : ∀ x, fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) (B x) (ys x) ⟶ I)
variable (δ' : ∀ x, fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) (B' x) (ys' x) ⟶ I)

def dependentOrder : AddressOrder (X × Y) (dependentWord xs ys) (dependentWord xs' ys') :=
  (rowOrders (fun x => (d x).relabel (Prod.mk x)) xs).seq
    (liftRows (fun x => (ys' x).map (Prod.mk x)) e)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1900000 in
include NL in
theorem dependentOrder_preserves
    [lF : ∀ x, (leftFactor T (A' x)).LaxBraided] (hl : ∀ x, SameLeftGather T (A' x) L)
    (hp : AddressOrder.mapSum additiveStructure A e ≫ act 𝒮 Zₐ (fun x => (p x).hom) xs' ≫ ε' = ε)
    (hq : ∀ x, AddressOrder.mapSum additiveStructure (B x) (d x) ≫ act 𝒮 Zₐ (fun y => (q x y).hom) (ys' x) ≫ δ' x = δ x) :
    AddressOrder.mapSum additiveStructure (dependentLabels (T:=T) A B) (dependentOrder e d) ≫
      act 𝒮 Zₐ (fun z : X × Y => T.map (p z.1).hom (q z.1 z.2).hom) (dependentWord xs' ys') ≫
        dependentWordAugCell R L J xs' ys' A' B' (indexedAugmentation δ') ε' =
      dependentWordAugCell R L J xs ys A B (indexedAugmentation δ) ε := by
  let S := dependentLabels (T:=T) A B
  let V := dependentLabels (T:=T) A' B'
  let r := dependentOrder e d
  let t := fun z : X × Y => T.map (p z.1).hom (q z.1 z.2).hom
  let e' := AddressOrder.mapSum additiveStructure A' e ≫ ε'
  let d' := fun x => AddressOrder.mapSum additiveStructure (B' x) (d x) ≫ δ' x
  have a : AddressOrder.mapSum additiveStructure S r ≫ act 𝒮 Zₐ t (dependentWord xs' ys') =
      act 𝒮 Zₐ t (dependentWord xs ys) ≫ AddressOrder.mapSum additiveStructure V r :=
    (AddressOrder.natural additiveNaturality t r).symm
  have b := dependentAug_parent_order R L J A' B' ys' e ε' δ'
  have c := dependentAug_child_order R L J A' B' xs d e' δ' hl
  have h₀ : act 𝒮 Zₐ (fun x => (p x).hom) xs ≫ e' = ε := by
    have h := AddressOrder.natural additiveNaturality (fun x => (p x).hom) e
    change act 𝒮 Zₐ (fun x => (p x).hom) xs ≫ AddressOrder.mapSum additiveStructure A' e =
      AddressOrder.mapSum additiveStructure A e ≫ act 𝒮 Zₐ (fun x => (p x).hom) xs' at h
    unfold e'
    rw [reassoc_of% h]
    exact hp
  have h₁ (x : X) : act 𝒮 Zₐ (fun y => (q x y).hom) (ys x) ≫ d' x = δ x := by
    have h := AddressOrder.natural additiveNaturality (fun y => (q x y).hom) (d x)
    change act 𝒮 Zₐ (fun y => (q x y).hom) (ys x) ≫ AddressOrder.mapSum additiveStructure (B' x) (d x) =
      AddressOrder.mapSum additiveStructure (B x) (d x) ≫ act 𝒮 Zₐ (fun y => (q x y).hom) (ys' x) at h
    unfold d'
    rw [reassoc_of% h]
    exact hq x
  have k := dependentAug_pointwise R L J NL xs ys (fun x => (p x).hom) (fun x y => (q x y).hom) ε e' δ d' h₀ h₁
  rw [reassoc_of% a]
  unfold r dependentOrder AddressOrder.mapSum
  simp only [Category.assoc]
  rw [b, c]
  exact k


set_option backward.isDefEq.respectTransparency false in
noncomputable def dependentOrderIso
    [lF : ∀ x, (leftFactor T (A' x)).LaxBraided] (hl : ∀ x, SameLeftGather T (A' x) L)
    (hp : AddressOrder.mapSum additiveStructure A e ≫ act 𝒮 Zₐ (fun x => (p x).hom) xs' ≫ ε' = ε)
    (hq : ∀ x, AddressOrder.mapSum additiveStructure (B x) (d x) ≫ act 𝒮 Zₐ (fun y => (q x y).hom) (ys' x) ≫ δ' x = δ x)
    (hn : (dependentWord xs ys).Nodup) :
    NativeAugmentedIso
      (dependentWordAug R L J xs ys A B (indexedAugmentation δ) ε)
      (dependentWordAug R L J xs' ys' A' B' (indexedAugmentation δ') ε') :=
  wordAugIso _ _ (dependentOrder e d) hn (structuralTensorIso (T:=T) p q) _ _
    (dependentOrder_preserves R L J NL e d p q ε ε' δ δ' hl hp hq)

set_option backward.isDefEq.respectTransparency false in
theorem dependentOrderIso_trace
    [lF : ∀ x, (leftFactor T (A' x)).LaxBraided] (hl : ∀ x, SameLeftGather T (A' x) L)
    (hp : AddressOrder.mapSum additiveStructure A e ≫ act 𝒮 Zₐ (fun x => (p x).hom) xs' ≫ ε' = ε)
    (hq : ∀ x, AddressOrder.mapSum additiveStructure (B x) (d x) ≫ act 𝒮 Zₐ (fun y => (q x y).hom) (ys' x) ≫ δ' x = δ x)
    (hn : (dependentWord xs ys).Nodup) (hn' : (dependentWord xs' ys').Nodup) :
    RawSingletonTrace
      (rawWordFrame (dependentLabels (T:=T) A B) (dependentWord xs ys) hn)
      (rawWordFrame (dependentLabels (T:=T) A' B') (dependentWord xs' ys') hn')
      (fun z => T.map (p z.1).hom (q z.1 z.2).hom)
      (dependentOrderIso R L J NL e d p q ε ε' δ δ' hl hp hq hn).hom.native :=
  wordAugIso_trace _ _ (dependentOrder e d) hn hn' (structuralTensorIso (T:=T) p q) _ _ _

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
