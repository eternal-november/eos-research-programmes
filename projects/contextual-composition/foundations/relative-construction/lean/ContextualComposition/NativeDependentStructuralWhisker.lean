module
public import ContextualComposition.NativeDependentUnitor
@[expose] public section

/-! Actual whiskering on common raw charts. The outer and inner
augmentation equations are consumed separately before assembly. -/
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
variable (J : UnitCompat R I) (NL : GatherLeftNat L)
variable {V V' : X → C} {W W' : X → Y → C}
variable (xs : List X) (ys : X → List Y)
variable (p : ∀ x, V x ≅ V' x) (q : ∀ x y, W x y ≅ W' x y)
variable (ε : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) V xs ⟶ I)
variable (ε' : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) V' xs ⟶ I)
variable (δ : ∀ x, fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) (W x) (ys x) ⟶ I)
variable (δ' : ∀ x, fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) (W' x) (ys x) ⟶ I)
variable (hp : act (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) (fun x => (p x).hom) xs ≫ ε' = ε)
variable (hq : ∀ x, act (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) (fun y => (q x y).hom) (ys x) ≫ δ' x = δ x)
variable (hn : (dependentWord xs ys).Nodup)

set_option backward.isDefEq.respectTransparency false in
/-- The tensor of coefficient isomorphisms; independent of any gather. -/
def structuralTensorIso (z : X × Y) : dependentLabels (T:=T) V W z ≅ dependentLabels (T:=T) V' W' z where
  hom := T.map (p z.1).hom (q z.1 z.2).hom
  inv := T.map (p z.1).inv (q z.1 z.2).inv
  hom_inv_id := by
    have e := T.map_seq (p z.1).hom (p z.1).inv (q z.1 z.2).hom (q z.1 z.2).inv
    change T.map ((p z.1).hom ≫ (p z.1).inv) ((q z.1 z.2).hom ≫ (q z.1 z.2).inv) = _ at e
    rw [Iso.hom_inv_id, Iso.hom_inv_id, T.map_id] at e
    exact e.symm
  inv_hom_id := by
    have e := T.map_seq (p z.1).inv (p z.1).hom (q z.1 z.2).inv (q z.1 z.2).hom
    change T.map ((p z.1).inv ≫ (p z.1).hom) ((q z.1 z.2).inv ≫ (q z.1 z.2).hom) = _ at e
    rw [Iso.inv_hom_id, Iso.inv_hom_id, T.map_id] at e
    exact e.symm

set_option backward.isDefEq.respectTransparency false in
/-- Whisker simultaneously through the actual dependent augmentation,
without splitting either whole augmentation into coefficient maps. -/
noncomputable def dependentWhiskerIso :
    NativeAugmentedIso
      (dependentWordAug R L J xs ys V W (indexedAugmentation δ) ε)
      (dependentWordAug R L J xs ys V' W' (indexedAugmentation δ') ε') :=
  wordAugIso _ _ (.ident (dependentWord xs ys)) hn (structuralTensorIso (T:=T) p q) _ _
    (by
      change 𝟙 _ ≫ act 𝒮 Zₐ _ _ ≫ _ = _
      rw [Category.id_comp]
      exact dependentAug_pointwise R L J NL xs ys _ _ ε ε' δ δ' hp hq)

set_option backward.isDefEq.respectTransparency false in
theorem dependentWhiskerIso_native :
    (dependentWhiskerIso R L J NL xs ys p q ε ε' δ δ' hp hq hn).hom.native =
      wordPointwise (dependentWord xs ys) (fun z => T.map (p z.1).hom (q z.1 z.2).hom) := by
  unfold dependentWhiskerIso
  exact wordAugIso_ident_pointwise _ hn (structuralTensorIso (T:=T) p q) _ _ _

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
