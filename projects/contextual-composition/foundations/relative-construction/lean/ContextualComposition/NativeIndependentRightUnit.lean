module
public import ContextualComposition.NativeIndependentSymmetry
@[expose] public section

/-! The original independent product with the singleton unit has the
same augmentation as the corresponding constant continuation unit. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)
variable {T : Bi (coeff (C:=C))} {I : C}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (J : UnitCompat R I)
variable {X : Type u} (A : X → C) (xs : List X)
variable (p : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) A xs ⟶ I)
set_option quotPrecheck false in
local notation "q" => (ρ_ I).hom

set_option backward.isDefEq.respectTransparency false in
theorem independentRightUnit_cell :
    rectangularWordAugCell R L (J.ρ I) A (fun _ : PUnit.{u+1} => I) xs ([PUnit.unit] : List PUnit.{u+1}) p q =
      dependentWordAugCell R L J xs (fun _ => ([PUnit.unit] : List PUnit.{u+1})) A (fun _ => (fun _ : PUnit.{u+1} => I)) (indexedAugmentation (fun _ => q)) p := by
  have h := dependentWordAug_raw_rows R L J xs (fun _ => ([PUnit.unit] : List PUnit.{u+1})) A (fun _ => (fun _ : PUnit.{u+1} => I)) (fun _ => q) p
  change dependentWordAugCell R L J xs (fun _ => ([PUnit.unit] : List PUnit.{u+1})) A (fun _ => (fun _ : PUnit.{u+1} => I)) (indexedAugmentation (fun _ => q)) p = _ at h
  rw [h]
  change rectWordChart (crossLabel T A (fun _ : PUnit.{u+1} => I)) xs ([PUnit.unit] : List PUnit.{u+1}) ≫ independentCell R L A (fun _ : PUnit.{u+1} => I) xs ([PUnit.unit] : List PUnit.{u+1}) p q ≫ J.ρ I =
    rectWordChart (crossLabel T A (fun _ : PUnit.{u+1} => I)) xs ([PUnit.unit] : List PUnit.{u+1}) ≫
      act 𝒮 Zₐ (fun x => (Lin.left L (A x)).collect (fun _ : PUnit.{u+1} => I) ([PUnit.unit] : List PUnit.{u+1}) ≫ T.map (𝟙 (A x)) q ≫ J.ρ (A x)) xs ≫ p
  let V := fold 𝒮 Zₐ A xs
  let W := fold 𝒮 Zₐ (fun _ : PUnit.{u+1} => I) ([PUnit.unit] : List PUnit.{u+1})
  let g₀ := DependentFibre.gather R A W xs
  let g₁ := DependentFibre.gather R A I xs
  let b (x : X) := (Lin.left L (A x)).collect (fun _ : PUnit.{u+1} => I) ([PUnit.unit] : List PUnit.{u+1})
  let l (x : X) := T.map (𝟙 (A x)) q
  let r (x : X) := J.ρ (A x)
  have m : T.map p q = T.map (𝟙 V) q ≫ T.map p (𝟙 I) := by
    change _ = (coeff (C:=C)).seq (T.map ((coeff (C:=C)).id V) q) (T.map p ((coeff (C:=C)).id I))
    rw [← T.map_seq, (coeff (C:=C)).id_seq, (coeff (C:=C)).seq_id]
  have n := J.natural p
  have g := gather_nat R A q xs
  have k := gather_unit J A xs
  change T.map p (𝟙 I) ≫ J.ρ I = J.ρ V ≫ p at n
  change g₀ ≫ T.map (𝟙 V) q = act 𝒮 Zₐ l xs ≫ g₁ at g
  change g₁ ≫ J.ρ V = act 𝒮 Zₐ r xs at k
  change _ ≫ ((act 𝒮 Zₐ b xs ≫ g₀) ≫ T.map p q) ≫ J.ρ I =
     _ ≫ act 𝒮 Zₐ (fun x => b x ≫ l x ≫ r x) xs ≫ p
  simp only [Category.assoc, m, n, reassoc_of% g, reassoc_of% k]
  have h₁ : act 𝒮 Zₐ l xs ≫ act 𝒮 Zₐ r xs = act 𝒮 Zₐ (fun x => l x ≫ r x) xs :=
    act_seq 𝒮 Zₐ l r xs
  rw [reassoc_of% h₁]
  have h₂ : act 𝒮 Zₐ b xs ≫ act 𝒮 Zₐ (fun x => l x ≫ r x) xs =
      act 𝒮 Zₐ (fun x => b x ≫ l x ≫ r x) xs := act_seq 𝒮 Zₐ b _ xs
  rw [reassoc_of% h₂]

set_option backward.isDefEq.respectTransparency false in
theorem unit_wordAug :
    AugHom.unit (S:=ℙ) I = wordAug (fun _ : PUnit.{u+1} => I) [PUnit.unit] q := by
  change (⟨terminalShape I, Hom.ident _⟩ : Aug ℙ I) = ⟨terminalShape I, _⟩
  congr 1
  apply native_hom_eq_of_cell_heq
  · funext j
    change (_ : Fin 1) = (_ : Fin 1)
    exact Subsingleton.elim _ _
  · intro j
    change HEq (standardPushSingle (fun _ : Fin 1 => I) j) (eqToHom (wordFoldPin (fun _ : PUnit.{u+1} => I) [PUnit.unit] j) ≫ q)
    exact HEq.rfl

set_option backward.isDefEq.respectTransparency false in
theorem independentRightUnit_aug :
    independentAug R L (J.ρ I) (wordAug A xs p) (AugHom.unit (S:=ℙ) I) =
      dependentWordAug R L J xs (fun _ => ([PUnit.unit] : List PUnit.{u+1})) A (fun _ => (fun _ : PUnit.{u+1} => I)) (indexedAugmentation (fun _ => q)) p := by
  have h := unit_wordAug (C:=C) (I:=I)
  rw [h, independentAug_ordered_eq, independentRightUnit_cell]
  rfl

/-- Forget precisely the one address of the multiplicative unit. -/
def singletonRightRead (X : Type u) : X × PUnit.{u+1} ≃ X :=
  ⟨Prod.fst, fun x => (x,PUnit.unit), fun ⟨_,_⟩ => rfl, fun _ => rfl⟩

omit [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] in
theorem singletonRightRead_word :
    xs.product ([PUnit.unit] : List PUnit.{u+1}) = xs.map (singletonRightRead X).symm :=
  flatMap_single_eq_map (fun x => (x,PUnit.unit)) xs

variable [lF : ∀ c : C, (leftFactor T c).LaxBraided]
variable (hl : ∀ c : C, SameLeftGather T c L)
variable (iρ : ∀ c : C, IsIso (J.ρ c))

set_option backward.isDefEq.respectTransparency false in
include hl in
noncomputable def independentRightUnit_read :
    WordAugReadComparison (fun z : X × PUnit.{u+1} => T.obj (A z.1) I) A (xs.product [PUnit.unit]) xs
      (rectangularWordAugCell R L (J.ρ I) A (fun _ => I) xs [PUnit.unit] p q) p := by
  let r := singletonRightRead X
  let f := fun x => T.obj (A x) I
  let u := xs.product ([PUnit.unit] : List PUnit.{u+1})
  let e := singletonRightRead_word xs
  let c := rectangularWordAugCell R L (J.ρ I) A (fun _ => I) xs [PUnit.unit] p q
  let t (z : X × PUnit.{u+1}) : f (r z) ≅ A (r z) := by
    let _ := iρ (A (r z))
    exact asIso (J.ρ (A (r z)))
  have w : u.map r = xs := (congrArg (List.map r) e).trans (equiv_word_read r xs)
  have h : wordAug (f ∘ r) u c = wordAug f xs (act 𝒮 Zₐ (fun x => J.ρ (A x)) xs ≫ p) := by
    dsimp only [c]
    rw [independentRightUnit_cell, singleton_indexedAugmentation_eq I]
    exact dependentWordAug_rightUnit_chart R L J xs A p (fun x => hl (A x))
  have H := wordAug_act_preserves_pullback r u xs w (fun x => J.ρ (A x)) c p h
  refine ⟨r,castOrder e,t,?_⟩
  let d := (std_fold_map A r (xs.map r.symm)).symm.trans
      (congrArg (fold 𝒮 Zₐ A) (equiv_word_read r xs))
  change AddressOrder.mapSum additiveStructure (f ∘ r) (castOrder e) ≫
      act 𝒮 Zₐ (fun z => J.ρ (A (r z))) (xs.map r.symm) ≫ eqToHom d ≫ p = c
  have step {u₀ v : List (X × PUnit.{u+1})} (e : u₀ = v) (w : u₀.map r = xs) :
      AddressOrder.mapSum additiveStructure (f ∘ r) (castOrder e) ≫ act 𝒮 Zₐ (fun z => J.ρ (A (r z))) v ≫
         eqToHom ((std_fold_map A r v).symm.trans
           (congrArg (fold 𝒮 Zₐ A) ((congrArg (List.map r) e).symm.trans w))) ≫ p =
      act 𝒮 Zₐ (fun z => J.ρ (A (r z))) u₀ ≫ eqToHom
        ((std_fold_map A r u₀).symm.trans (congrArg (fold 𝒮 Zₐ A) w)) ≫ p := by
    subst v
    simp only [castOrder_map, eqToHom_refl, Category.id_comp]
  exact (step e w).trans H

set_option backward.isDefEq.respectTransparency false in
noncomputable def independentRightUnitIso (hx : xs.Nodup) :
    NativeAugmentedIso (independentAug R L (J.ρ I) (wordAug A xs p) (AugHom.unit (S:=ℙ) I))
      (wordAug A xs p) :=
  let o := independentRightUnit_read R L J A xs p (hl:=hl) (iρ:=iρ)
  (o.toIso (nodup_product_word hx (by simp))).retarget
    ((independentAug_ordered_eq R L (J.ρ I) A (fun _ : PUnit.{u+1} => I) xs [PUnit.unit] p q).symm.trans
      (congrArg (independentAug R L (J.ρ I) (wordAug A xs p)) unit_wordAug.symm)) rfl

set_option backward.isDefEq.respectTransparency false in
theorem independentRightUnitIso_trace (hx : xs.Nodup) :
    let U : RawSingletonFrame PUnit.{u+1} (terminalShape I) :=
      rawWordFrame (fun _ : PUnit.{u+1} => I) [PUnit.unit] (by simp)
    let F := (rawWordFrame A xs hx).tensor T U
    let e := singletonRightRead X
    let G := (rawWordFrame A xs hx).relabel e.symm e.symm.injective (A ∘ e) (fun _ => rfl)
    RawSingletonTrace F G (fun z => J.ρ (A z.1))
      (independentRightUnitIso R L J A xs p hl iρ hx).hom.native := by
  intro U F e G
  let B := fun _ : PUnit.{u+1} => I
  let ys : List PUnit.{u+1} := [PUnit.unit]
  let hn := nodup_product_word hx (show ys.Nodup by simp [ys])
  let o := independentRightUnit_read R L J A xs p (hl:=hl) (iρ:=iρ)
  let F₀ := rawWordFrame (crossLabel T A B) (xs.product ys) hn
  let d : independentFamily T (wordFamily A xs) (terminalShape I) = wordFamily (crossLabel T A B) (xs.product ys) :=
    independentFamily_word (T:=T) A B xs ys
  have k : HEq (o.toIso hn).hom.native (independentRightUnitIso R L J A xs p hl iρ hx).hom.native := by
    unfold independentRightUnitIso
    exact (NativeAugmentedIso.retarget_native_heq _ _ rfl).symm
  have r (j : Fin _) : F.read j = F₀.read (Fin.cast (congrArg Family.n d) j) :=
    frame_tensor_read_cast (rawWordFrame A xs hx) U rfl rfl (fun _ => rfl) (fun _ => rfl) j
  exact (o.toIso_trace hn hx).retarget d.symm rfl k (rawFrame_read_reverse F F₀ d r)
    (fun _ => rfl) (fun _ => HEq.rfl)

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
