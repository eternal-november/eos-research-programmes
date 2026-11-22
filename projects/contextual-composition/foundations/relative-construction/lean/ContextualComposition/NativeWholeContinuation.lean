module
public import ContextualComposition.NativeIndependentRect

@[expose] public section
/-! The whole target continuation used by a many-to-one parent merge
is computed from the actual native continuation map. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v w
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "ℙ" => standardPush
local notation "𝒮" => binary (Additive.sum Additive.ofBraided)
local notation "Zₐ" => 𝟙_ _

noncomputable def wholeContinuation {A B : Family C} (p : Hom ℙ A B) :
    totalFold A ⟶ totalFold B :=
  AddressOrder.mapSum additiveStructure A.val (totalPartitionOrder p.addr) ≫
    rowsChart A.val (fibreList p.addr) (List.finRange B.n) ≫
    act 𝒮 Zₐ p.cell (List.finRange B.n)

set_option backward.isDefEq.respectTransparency false in
theorem wholeContinuation_preserves {A B : Family C} {I : C}
    {δ : totalFold A ⟶ I} {q : totalFold B ⟶ I}
    (p : AugHom ℙ (totalAug A δ) (totalAug B q)) :
    wholeContinuation p.native ≫ q = δ := by
  simpa only [wholeContinuation, Category.assoc] using
    (totalAug_preserving_iff p.native δ q).mp p.preserves

set_option backward.isDefEq.respectTransparency false in
theorem wholeContinuation_is_total {A B : Family C} (p : Hom ℙ A B) {I : C} (q : totalFold B ⟶ I) :
    p.comp (totalAug B q).ε = (totalAug A (wholeContinuation p ≫ q)).ε := by
  apply (totalAug_preserving_iff p (wholeContinuation p ≫ q) q).mpr
  simp only [wholeContinuation, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
theorem wholeContinuation_comp {A B D : Family C} (p : Hom ℙ A B) (q : Hom ℙ B D) :
    wholeContinuation (p.comp q) = wholeContinuation p ≫ wholeContinuation q := by
  let d := 𝟙 (totalFold D)
  let b := wholeContinuation q ≫ d
  have h : (p.comp q).comp (totalAug D d).ε =
      (totalAug A (wholeContinuation p ≫ b)).ε := by
    rw [Hom.comp_assoc, wholeContinuation_is_total q d]
    exact wholeContinuation_is_total p b
  have e := (totalAug_preserving_iff (p.comp q) (wholeContinuation p ≫ b) d).mp h
  have ee : wholeContinuation (p.comp q) ≫ d = wholeContinuation p ≫ b := by
    simpa only [wholeContinuation, Category.assoc] using e
  simpa only [b, d, Category.comp_id] using ee

variable {T : Bi (coeff (C:=C))} {I : C}

set_option backward.isDefEq.respectTransparency false in
/-- Many-to-one parent coefficient aggregation with arbitrary, independently
carrier-changing native continuation arrows.  The source-row augmentation
law here is derived, not supplied.  The outer whole-fibre map stays opaque.
The input equalities merely read the chosen native source words in the
older coefficient theorem's row presentation. -/
theorem native_whole_continuation_merge (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    (U : UnitCompat R I) {X : Type w}
    (V : X → C) (J : Input X C) (xs : List X)
    (A : X → Family C) (B : Family C)
    (pin : ∀ x, inner (S:=𝒮) (Z:=Zₐ) J x = totalFold (A x))
    (δ : ∀ x, totalFold (A x) ⟶ I) (q : totalFold B ⟶ I)
    (p : ∀ x ∈ xs, AugHom ℙ (totalAug (A x) (δ x)) (totalAug B q))
    {a : C} (α : fold 𝒮 Zₐ V xs ⟶ a) :
    localDep (G:=R) L V J xs α (fun x hx => eqToHom (pin x) ≫ wholeContinuation (p x hx).native) ≫
        (T.map (𝟙 a) q ≫ U.ρ a) =
      act 𝒮 Zₐ (sourceRow L U V J (fun x => eqToHom (pin x) ≫ δ x)) xs ≫ α := by
  refine localAug (K:=coeff (C:=C)) L U V J xs α _ _ q ?_
  intro x hx
  change (eqToHom (pin x) ≫ wholeContinuation (p x hx).native) ≫ q =
    eqToHom (pin x) ≫ δ x
  rw [Category.assoc, wholeContinuation_preserves (p x hx)]

set_option backward.isDefEq.respectTransparency false in
theorem wholeContinuation_ident (A : Family C) :
    wholeContinuation (Hom.ident (S:=ℙ) A) = 𝟙 (totalFold A) := by
  have h := Hom.ident_comp (totalAug A (𝟙 (totalFold A))).ε
  have e := (totalAug_preserving_iff (Hom.ident (S:=ℙ) A) (𝟙 (totalFold A)) (𝟙 (totalFold A))).mp h
  have ee : wholeContinuation (Hom.ident (S:=ℙ) A) ≫ 𝟙 (totalFold A) = 𝟙 (totalFold A) := by
    simpa only [wholeContinuation, Category.assoc] using e
  simpa only [Category.comp_id] using ee

section Global
variable (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ) (U : UnitCompat R I)
variable {P Q : Family C} {ε₁ : totalFold P ⟶ I} {ε₂ : totalFold Q ⟶ I}
variable (o : AugHom ℙ (totalAug P ε₁) (totalAug Q ε₂))
variable (A : Fin P.n → Family C) (B : Fin Q.n → Family C)
variable (δ : ∀ i, totalFold (A i) ⟶ I) (η : ∀ j, totalFold (B j) ⟶ I)
variable (c : ∀ j, ∀ i ∈ fibreList o.native.addr j, AugHom ℙ (totalAug (A i) (δ i)) (totalAug (B j) (η j)))
variable (J : Input (Fin P.n) C)
variable (pin : ∀ i, inner (S:=𝒮) (Z:=Zₐ) J i = totalFold (A i))

noncomputable def nativeWholeParentBlock (j : Fin Q.n) :
    fold 𝒮 Zₐ (rowSource (S:=𝒮) (T:=T) (Z:=Zₐ) P.val J) (fibreList o.native.addr j) ⟶
      T.obj (Q.val j) (totalFold (B j)) :=
  localDep (G:=R) L P.val J (fibreList o.native.addr j) (o.native.cell j)
    (fun i hi => eqToHom (pin i) ≫ wholeContinuation (c j i hi).native)

set_option backward.isDefEq.respectTransparency false in
/-- A global many-to-one parent regrouping against the original single
outer augmentation. The source starts as the flat word of whole attached
rows, the regrouping is the exact native parent partition, and each
continuation can change carrier into its target parent's continuation.
This does not yet flatten each continuation into its individual leaves. -/
theorem native_whole_parent_paste :
    let w := List.finRange Q.n
    let f := o.native.addr
    let X := rowSource (S:=𝒮) (T:=T) (Z:=Zₐ) P.val J
    let h := sourceRow L U P.val J (fun i => eqToHom (pin i) ≫ δ i)
    AddressOrder.mapSum additiveStructure X (totalPartitionOrder f) ≫
      rowsChart X (fibreList f) w ≫
      act 𝒮 Zₐ (nativeWholeParentBlock R L o A B δ η c J pin) w ≫
      act 𝒮 Zₐ (fun j => T.map (𝟙 (Q.val j)) (η j) ≫ U.ρ (Q.val j)) w ≫ ε₂ =
      act 𝒮 Zₐ h (List.finRange P.n) ≫ ε₁ := by
  intro w f X h
  let o₀ : Hom ℙ P Q := o.native
  let z := fun j => T.map (𝟙 (Q.val j)) (η j) ≫ U.ρ (Q.val j)
  let b := nativeWholeParentBlock R L o A B δ η c J pin
  have H (j : Fin Q.n) : b j ≫ z j =
      act 𝒮 Zₐ h (fibreList f j) ≫ o₀.cell j :=
    native_whole_continuation_merge R L U P.val J (fibreList f j) A (B j) pin δ (η j) (c j) (o₀.cell j)
  let r := AddressOrder.mapSum additiveStructure X (totalPartitionOrder f)
  let r' := AddressOrder.mapSum additiveStructure P.val (totalPartitionOrder f)
  let s := rowsChart X (fibreList f) w
  let s' := rowsChart P.val (fibreList f) w
  let a := act 𝒮 Zₐ h (w.flatMap (fibreList f))
  let a' := act 𝒮 Zₐ h (List.finRange P.n)
  let v := act 𝒮 Zₐ (fun j => act 𝒮 Zₐ h (fibreList f j)) w
  let k := act 𝒮 Zₐ o₀.cell w
  change r ≫ s ≫ act 𝒮 Zₐ b w ≫ act 𝒮 Zₐ z w ≫ ε₂ = a' ≫ ε₁
  have ha : act 𝒮 Zₐ b w ≫ act 𝒮 Zₐ z w = v ≫ k := by
    exact (act_seq 𝒮 Zₐ b z w).trans
      ((congrArg (fun p => act 𝒮 Zₐ p w) (funext H)).trans
        (act_seq 𝒮 Zₐ (fun j => act 𝒮 Zₐ h (fibreList f j)) o₀.cell w).symm)
  have hs : s ≫ v = a ≫ s' := (rowsChart_natural (fibreList f) h w).symm
  have hr : r ≫ a = a' ≫ r' :=
    (AddressOrder.natural additiveNaturality h (totalPartitionOrder f)).symm
  have he : r' ≫ s' ≫ k ≫ ε₂ = ε₁ := by
    have e : wholeContinuation o₀ ≫ ε₂ = ε₁ := wholeContinuation_preserves o
    simpa only [wholeContinuation, Category.assoc] using e
  rw [← Category.assoc (act 𝒮 Zₐ b w), ha]
  simp only [Category.assoc]
  rw [reassoc_of% hs, reassoc_of% hr, he]

end Global

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
