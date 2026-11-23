module
public import ContextualComposition.NativeDependentPentagonChart
@[expose] public section

/-! Alignment of actual augmentation comparisons through exact ordered
raw reads. This is a change of occurrence alphabets, not a permutation. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v w z
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)

set_option backward.isDefEq.respectTransparency false in
/-- Carry a pointwise augmentation preservation equation to another raw
alphabet. The original morphism on each occurrence is read untouched. -/
theorem wordAct_preservation_read {X : Type w} {Y : Type z} {I : C}
    {A B : Y → C} (g : X → Y) (xs : List X) (ys : List Y) (h : xs.map g = ys)
    (p : ∀ y, A y ⟶ B y)
    {a : fold 𝒮 Zₐ A ys ⟶ I} {b : fold 𝒮 Zₐ B ys ⟶ I}
    {a₀ : fold 𝒮 Zₐ (A ∘ g) xs ⟶ I} {b₀ : fold 𝒮 Zₐ (B ∘ g) xs ⟶ I}
    (ha : HEq a₀ a) (hb : HEq b₀ b)
    (e : act 𝒮 Zₐ p ys ≫ b = a) :
    act 𝒮 Zₐ (fun x => p (g x)) xs ≫ b₀ = a₀ := by
  subst ys
  let eA := std_fold_map A g xs
  let eB := std_fold_map B g xs
  have h₀ : HEq (act 𝒮 Zₐ (fun x => p (g x)) xs ≫ b₀) (act 𝒮 Zₐ p (xs.map g) ≫ b) :=
    structural_seq_heq (K:=coeff (C:=C)) eA.symm eB.symm rfl (actRetag_heq g p xs) hb
  exact eq_of_heq (h₀.trans ((heq_of_eq e).trans ha.symm))

set_option backward.isDefEq.respectTransparency false in
theorem wordPointwise_retag_heq {X : Type w} {Y : Type z} {A B : Y → C}
    (g : X → Y) (xs : List X) (ys : List Y) (h : xs.map g = ys)
    (p : ∀ y, A y ⟶ B y) :
    HEq (wordPointwise xs (fun x => p (g x))) (wordPointwise ys p) := by
  subst ys
  have transport {n m : Nat} (e : n = m) {A₁ B₁ : Fin n → C} {A₂ B₂ : Fin m → C}
      (p₁ : ∀ j, A₁ j ⟶ B₁ j) (p₂ : ∀ j, A₂ j ⟶ B₂ j)
      (ha : ∀ j, A₁ j = A₂ (Fin.cast e j)) (hb : ∀ j, B₁ j = B₂ (Fin.cast e j))
      (hp : ∀ j, HEq (p₁ j) (p₂ (Fin.cast e j))) :
      HEq
        (nativeSingletonMap (A:=Family.mk n A₁) (B:=Family.mk n B₁) (Equiv.refl _) p₁)
        (nativeSingletonMap (A:=Family.mk m A₂) (B:=Family.mk m B₂) (Equiv.refl _) p₂) := by
    subst m
    have ea : A₁ = A₂ := funext ha
    have eb : B₁ = B₂ := funext hb
    subst A₂
    subst B₂
    exact heq_of_eq (congrArg (nativeSingletonMap (A:=Family.mk n A₁) (B:=Family.mk n B₁) (Equiv.refl _)) (funext fun j => eq_of_heq (hp j)))
  let k := (List.length_map g (as:=xs)).symm
  have read (j : Fin xs.length) : g xs[j] = (xs.map g)[Fin.cast k j] := retag_word_get g xs rfl j
  unfold wordPointwise wordFamily
  exact transport k _ _ (fun j => congrArg A (read j)) (fun j => congrArg B (read j))
    (fun j => by
      have aux {a b : Y} (e : a = b) : HEq (p a) (p b) := by subst b; rfl
      exact aux (read j))


variable {T : Bi (coeff (C:=C))} {I : C}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (J : UnitCompat R I) (P : TensorPrimitive T)
variable (NL : GatherLeftNat L) (Q : PrimitiveLinearity R L P) (U : AssocRightUnit R J P)
variable [lF : ∀ a : C, (leftFactor T a).LaxBraided]
variable (hl : ∀ a : C, SameLeftGather T a L)
variable {X Y W : Type u} (xs : List X) (ys : X → List Y) (ws : X → Y → List W)
variable (V : X → C) (B : X → Y → C) (D : X → Y → W → C)

set_option backward.isDefEq.respectTransparency false in
theorem dependentAssocIso_pointwise_heq
    (ε : fold 𝒮 Zₐ V xs ⟶ I) (δ : ∀ x, fold 𝒮 Zₐ (B x) (ys x) ⟶ I)
    (γ : ∀ x y, fold 𝒮 Zₐ (D x y) (ws x y) ⟶ I)
    (ι : ∀ a b c, IsIso (P.assoc a b c))
    (hn : (dependentWord xs (fun x => dependentWord (ys x) (ws x))).Nodup) :
    HEq (dependentAssocIso R L J P NL Q U xs ys ws V B D ε δ γ hl ι hn).hom.native
      (wordPointwise (dependentWord xs (fun x => dependentWord (ys x) (ws x)))
        (fun z : X × Y × W => P.assoc (V z.1) (B z.1 z.2.1) (D z.1 z.2.1 z.2.2))) := by
  apply (dependentAssocIso_frame_heq P V B D R L J NL Q U hl xs ys ws ε δ γ ι hn).trans
  exact heq_of_eq (wordReindex_ident_pointwise _ hn (associatorTripleIso P V B D ι))


set_option backward.isDefEq.respectTransparency false in
include NL Q U hl in
theorem dependentAssoc_preserves_pullback
    (ε : fold 𝒮 Zₐ V xs ⟶ I) (δ : ∀ x, fold 𝒮 Zₐ (B x) (ys x) ⟶ I)
    (γ : ∀ x y, fold 𝒮 Zₐ (D x y) (ws x y) ⟶ I) :
    let w₀ := dependentWord (dependentWord xs ys) (fun p => ws p.1 p.2)
    let _w₁ := dependentWord xs (fun x => dependentWord (ys x) (ws x))
    let A₁ := assocRightLabels T V B D
    let e := (std_fold_map A₁ tripleRetag w₀).symm.trans
      (congrArg (fold 𝒮 Zₐ A₁) (tripleRetag_word xs ys ws))
    act 𝒮 Zₐ (fun a : (X × Y) × W => P.assoc (V a.1.1) (B a.1.1 a.1.2) (D a.1.1 a.1.2 a.2)) w₀ ≫
      eqToHom e ≫ dependentAssocRightAug R L J xs ys ws V B D ε δ γ =
      dependentAssocLeftAug R L J xs ys ws V B D ε δ γ := by
  intro w₀ w₁ A₁ e
  let A₀ := assocLeftLabels T V B D ∘ tripleRetag.symm
  let g := tripleRetag (X:=X) (Y:=Y) (W:=W)
  let p := fun z : X × Y × W => P.assoc (V z.1) (B z.1 z.2.1) (D z.1 z.2.1 z.2.2)
  let a := dependentAssocLeftAug R L J xs ys ws V B D ε δ γ
  let b := dependentAssocRightAug R L J xs ys ws V B D ε δ γ
  let pin := (std_fold_map A₀ g w₀).symm.trans (congrArg (fold 𝒮 Zₐ A₀) (tripleRetag_word xs ys ws))
  have h : a = eqToHom pin ≫ act 𝒮 Zₐ p w₁ ≫ b :=
    dependentAssoc_augmentation R L J P NL Q U xs ys ws V B D ε δ γ hl
  have ha : HEq a (act 𝒮 Zₐ p w₁ ≫ b) := (heq_of_eq h).trans (hom_source_pin_heq pin _)
  exact wordAct_preservation_read g w₀ w₁ (tripleRetag_word xs ys ws) p ha
    (hom_source_pin_heq e b) rfl

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
