module
public import ContextualComposition.NativeFubiniWordComparison
@[expose] public section

/-! Transport scalar Fubini preservation into an arbitrary address
presentation, including dormant rows whose words need not be nodup.
No native comparison is asserted on a repeated-address word. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2100000 in
def WordAugReadComparison.ofScalarOrder {X Y Z : Type u} {I : C} {A : X → C} {B : Y → C}
    (f : X ≃ Y) (g : Z → X) (xs : List X) (ys : List Y) (u v : List Z)
    (hu : u.map g = xs) (hv : v.map (f ∘ g) = ys)
    (φ : ∀ x, A x ≅ B (f x))
    (a : fold 𝒮 Zₐ A xs ⟶ I) (b : fold 𝒮 Zₐ B ys ⟶ I)
    (a₀ : fold 𝒮 Zₐ (A ∘ g) u ⟶ I) (b₀ : fold 𝒮 Zₐ (B ∘ f ∘ g) v ⟶ I)
    (ha : HEq a a₀) (hb : HEq b b₀) (p : AddressOrder Z u v)
    (h : AddressOrder.mapSum additiveStructure (A ∘ g) p ≫
      act 𝒮 Zₐ (fun x => (φ (g x)).hom) v ≫ b₀ = a₀) :
    WordAugReadComparison A B xs ys a b := by
  have ht : v.map g = ys.map f.symm := by
    rw [← hv, List.map_map]
    congr 1
    funext z
    exact (f.symm_apply_apply (g z)).symm
  let w := ys.map f.symm
  let H := B ∘ f
  let E₁ := (std_fold_map B f w).symm.trans (congrArg (fold 𝒮 Zₐ B) (equiv_word_read f ys))
  let E₂ := congrArg (fold 𝒮 Zₐ H) ht
  let E₀ := std_fold_map H g v
  let C₀ := congrArg (fold 𝒮 Zₐ A) hu.symm
  let C₁ := std_fold_map A g u
  let L₀ := fun x => (φ x).hom
  let a₁ := eqToHom (C₀.trans C₁) ≫ a₀
  let b₁ := eqToHom (E₀.symm.trans (E₂.trans E₁)) ≫ b
  let o := (castOrder hu.symm).seq ((p.relabel g).seq (castOrder ht))
  refine ⟨f,o,φ,?_⟩
  have aEq : a = a₁ := eq_of_heq (ha.trans (hom_source_pin_heq _ a₀).symm)
  have bEq : b₁ = b₀ := eq_of_heq ((hom_source_pin_heq _ b).trans hb)
  -- The same source and target fold pins occur on both sides of the
  -- relabelled order.  Move pointwise maps before cancelling the pins.
  have nn : eqToHom (congrArg (fold 𝒮 Zₐ A) ht) ≫ act 𝒮 Zₐ L₀ w =
      act 𝒮 Zₐ L₀ (v.map g) ≫ eqToHom E₂ := by
    have z {v₀ w₀ : List X} (t : v₀ = w₀) :
        eqToHom (congrArg (fold 𝒮 Zₐ A) t) ≫ act 𝒮 Zₐ L₀ w₀ =
        act 𝒮 Zₐ L₀ v₀ ≫ eqToHom (congrArg (fold 𝒮 Zₐ H) t) := by
      subst w₀
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    exact z ht
  have hact : act 𝒮 Zₐ L₀ (v.map g) ≫ eqToHom E₂ ≫ eqToHom E₁ ≫ b =
      eqToHom (std_fold_map A g v) ≫ act 𝒮 Zₐ (fun x => L₀ (g x)) v ≫ b₀ := by
    -- Express the remaining source pin as the standard map of the read.
    have k : eqToHom E₂ ≫ eqToHom E₁ ≫ b = eqToHom E₀ ≫ b₀ := by
      rw [← bEq]
      unfold b₁
      rw [eqToHom_trans_assoc, eqToHom_trans_assoc]
    rw [k, ← Category.assoc]
    simpa only [Category.assoc] using congrArg (fun t => t ≫ b₀) (std_act_map A g L₀ v).symm
  have hsum := relabel_mapSum A g p
  change AddressOrder.mapSum additiveStructure A o ≫ act 𝒮 Zₐ L₀ w ≫ eqToHom E₁ ≫ b = a
  rw [aEq]
  unfold o
  simp only [AddressOrder.mapSum, Category.assoc, castOrder_map]
  rw [reassoc_of% nn, hact, ← Category.assoc (AddressOrder.mapSum additiveStructure A (p.relabel g)),
    ← hsum]
  simp only [Category.assoc]
  change AddressOrder.mapSum additiveStructure (fun i => A (g i)) p ≫ act 𝒮 Zₐ (fun x => L₀ (g x)) v ≫ b₀ = a₀ at h
  rw [h, eqToHom_trans_assoc]


variable {T : Bi (coeff (C:=C))} {I : C}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (J : UnitCompat R I)
variable (N : GridBinary (symmetricCross (C:=C)) R L) (NR : GatherOuterNat R) (NL : GatherLeftNat L)
variable (m : Middle T I) (mi : MiddleInv m) (h : MedialLinear m R L) (j : MedialInner m R L)
variable (unit_middle : m.cell I I I I ≫ unitCollapse R J = unitCollapse R J)
variable [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
variable (hl : ∀ a : C, SameLeftGather T a L) (hr : ∀ b : C, SameRightGather R b)
variable {X U Y W : Type u}
variable (xs : List X) (ys : List Y) (us : X → List U) (vs : Y → List W)
variable (V : X → C) (P : Y → C) (A : X → U → C) (B : Y → W → C)
variable (δ : ∀ x, fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) (A x) (us x) ⟶ I)
variable (η : ∀ y, fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) (B y) (vs y) ⟶ I)
variable (ε : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) V xs ⟶ I)
variable (γ : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) P ys ⟶ I)

def separateRawPairCell :=
  rectangularWordAugCell R L (J.ρ I) (dependentLabels (T:=T) V A) (dependentLabels (T:=T) P B)
    (dependentWord xs us) (dependentWord ys vs)
    (dependentWordAugCell R L J xs us V A (indexedAugmentation δ) ε)
    (dependentWordAugCell R L J ys vs P B (indexedAugmentation η) γ)

def jointRawPairCell :=
  dependentWordAugCell R L J (xs.product ys) (crossChildWord us vs) (crossLabel T V P) (crossChildLabel T A B)
    (indexedAugmentation (fun z => rectangularWordAugCell R L (J.ρ I) (A z.1) (B z.2)
      (us z.1) (vs z.2) (δ z.1) (η z.2)))
    (rectangularWordAugCell R L (J.ρ I) V P xs ys ε γ)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3300000 in
noncomputable def binaryFubini_scalarComparison :
    WordAugReadComparison (crossLabel T (dependentLabels (T:=T) V A) (dependentLabels (T:=T) P B))
      (dependentLabels (T:=T) (crossLabel T V P) (crossChildLabel T A B))
      ((dependentWord xs us).product (dependentWord ys vs)) (dependentWord (xs.product ys) (crossChildWord us vs))
      (separateRawPairCell R L J xs ys us vs V P A B δ η ε γ)
      (jointRawPairCell R L J xs ys us vs V P A B δ η ε γ) := by
  let X₀ := (X × U) × (Y × W)
  let Y₀ := (X × Y) × (U × W)
  let Z₀ := X × U × Y × W
  let i : X₀ ≃ Z₀ := ⟨pairQuad, fun t => ((t.1,t.2.1),(t.2.2.1,t.2.2.2)), fun _ => rfl, fun _ => rfl⟩
  let k : Y₀ ≃ Z₀ := jointPairRetag
  let f := i.trans k.symm
  let g := i.symm
  let u := (fourOccurrenceExpr xs ys us vs).leaves
  let v := (fourJointExpr xs ys us vs).leaves
  let w₀ := (dependentWord xs us).product (dependentWord ys vs)
  let w₁ := dependentWord (xs.product ys) (crossChildWord us vs)
  let S := crossLabel T (dependentLabels (T:=T) V A) (dependentLabels (T:=T) P B)
  let D := dependentLabels (T:=T) (crossLabel T V P) (crossChildLabel T A B)
  let φ (t : X₀) : S t ≅ D (f t) := binaryLeafIso V P A B m mi (i t)
  have e₀ : u.map g = w₀ := by
    have h₀ : w₀.map i = u := nativeOccurrenceExpr_word_product xs ys us vs
    rw [← h₀]
    exact equiv_word_read i.symm w₀
  have e₁ : v.map (f ∘ g) = w₁ := by
    have h₁ : w₁.map k = v := jointPairRetag_word xs ys us vs
    rw [← h₁]
    exact equiv_word_read k.symm w₁
  let a := separateRawPairCell R L J xs ys us vs V P A B δ η ε γ
  let b := jointRawPairCell R L J xs ys us vs V P A B δ η ε γ
  let c := separateWordAug xs ys us vs V P A B R L J (indexedAugmentation δ) (indexedAugmentation η) ε γ
  let d := jointWordAug xs ys us vs V P A B R L J (indexedAugmentation δ) (indexedAugmentation η) ε γ
  have hz₀ := separateProductAug_eq R L J xs ys us vs V P A B δ η ε γ hl hr
  have hh := independentAug_ordered_eq R L (J.ρ I) (dependentLabels (T:=T) V A) (dependentLabels (T:=T) P B)
    (dependentWord xs us) (dependentWord ys vs)
    (dependentWordAugCell R L J xs us V A (indexedAugmentation δ) ε)
    (dependentWordAugCell R L J ys vs P B (indexedAugmentation η) γ)
  have ea : HEq a c := wordAug_cell_heq a c (hh.symm.trans hz₀)
  have eb : HEq b d := wordAug_cell_heq b d (jointProductAug_eq R L J xs ys us vs V P A B δ η ε γ hl hr)
  exact WordAugReadComparison.ofScalarOrder f g w₀ w₁ u v e₀ e₁ φ a b c d ea eb
    (gridOrder (fourExchangeChart xs ys us vs))
    (binary_word_aug_preserving xs ys us vs V P A B R L N NR NL J m
      (indexedAugmentation δ) (indexedAugmentation η) ε γ mi h j unit_middle)


set_option backward.isDefEq.respectTransparency false in
def WordAugReadComparison.scalarIdent {X : Type u} {I : C} (A : X → C) (xs : List X)
    (a : fold 𝒮 Zₐ A xs ⟶ I) :
    WordAugReadComparison A A xs xs a a := by
  have hi : act 𝒮 Zₐ (fun x => 𝟙 (A x)) xs = 𝟙 _ := act_id_grid xs
  exact WordAugReadComparison.ofScalarOrder (Equiv.refl X) id xs xs xs xs
    (List.map_id xs) (List.map_id xs) (fun x => Iso.refl (A x)) a a a a HEq.rfl HEq.rfl
    (.ident xs) (by
      change 𝟙 _ ≫ act 𝒮 Zₐ (fun x => 𝟙 (A x)) xs ≫ a = a
      rw [hi, Category.id_comp, Category.id_comp])

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
