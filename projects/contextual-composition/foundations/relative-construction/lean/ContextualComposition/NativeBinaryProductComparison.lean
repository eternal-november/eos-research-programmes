module
public import ContextualComposition.NativeOrderedRectProduct
@[expose] public section

/-! The literal binary comparison on product and accumulation endpoints. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)

section BinaryObject
variable {T : Bi (coeff (C:=C))} {I : C}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (J : UnitCompat R I)
variable {X U Y W : Type u}
variable (xs : List X) (ys : List Y) (us : X → List U) (vs : Y → List W)
variable (V : X → C) (P : Y → C) (A : X → U → C) (B : Y → W → C)
variable (δ : ∀ x, fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) (A x) (us x) ⟶ I)
variable (η : ∀ y, fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) (B y) (vs y) ⟶ I)
variable (ε : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) V xs ⟶ I)
variable (γ : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) P ys ⟶ I)

set_option backward.isDefEq.respectTransparency false in
theorem separateProductAug_eq
    [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
    (hl : ∀ a : C, SameLeftGather T a L) (hr : ∀ b : C, SameRightGather R b) :
    independentAug R L (J.ρ I)
      (dependentWordAug R L J xs us V A (indexedAugmentation δ) ε)
      (dependentWordAug R L J ys vs P B (indexedAugmentation η) γ) =
    wordAug (separateLeafLabels (T:=T) V P A B) (fourOccurrenceExpr xs ys us vs).leaves
      (separateWordAug xs ys us vs V P A B R L J (indexedAugmentation δ) (indexedAugmentation η) ε γ) := by
  let xw := dependentWord xs us
  let yw := dependentWord ys vs
  let F := dependentLabels (T:=T) V A
  let G := dependentLabels (T:=T) P B
  let p := dependentWordAugCell R L J xs us V A (indexedAugmentation δ) ε
  let q := dependentWordAugCell R L J ys vs P B (indexedAugmentation η) γ
  let H := separateLeafLabels (T:=T) V P A B
  let s := independentWord (wordFamily F xw) (wordFamily G yw)
  let t := (fourOccurrenceExpr xs ys us vs).leaves
  let r := quadRead xw yw
  change wordAug (H ∘ r) s (independentWordAugCell T R L (wordFamily F xw) (wordFamily G yw)
    (totalNativeCell (wordAug F xw p)) (totalNativeCell (wordAug G yw q)) (J.ρ I)) = _
  apply wordAug_read_eq H r s t (quadRead_word xs ys us vs)
  rw [totalNativeCell_wordAug, totalNativeCell_wordAug]
  exact independentDependentAugCell_heq R L V P A B xs ys us vs hl hr J
    (indexedAugmentation δ) (indexedAugmentation η) ε γ

set_option backward.isDefEq.respectTransparency false in
theorem jointProductAug_eq
    [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
    (hl : ∀ a : C, SameLeftGather T a L) (hr : ∀ b : C, SameRightGather R b) :
    dependentWordAug R L J (xs.product ys) (crossChildWord us vs) (crossLabel T V P) (crossChildLabel T A B)
      (indexedAugmentation (fun z => rectangularWordAugCell R L (J.ρ I) (A z.1) (B z.2)
        (us z.1) (vs z.2) (δ z.1) (η z.2)))
      (rectangularWordAugCell R L (J.ρ I) V P xs ys ε γ) =
    wordAug (jointLeafLabels (T:=T) V P A B) (fourJointExpr xs ys us vs).leaves
      (jointWordAug xs ys us vs V P A B R L J (indexedAugmentation δ) (indexedAugmentation η) ε γ) := by
  have h := jointDependentWordAug_eq R L J xs ys us vs V P A B
    (indexedAugmentation δ) (indexedAugmentation η) ε γ hl (hr _)
  have hp {a b : C} (f : a = b) (p : b ⟶ I) : eqToHom f.symm ≫ eqToHom f ≫ p = p := by
    rw [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
  dsimp only at h
  simp only [jointProductChildAug, jointIndexedChildCell, indexedAugmentation, hp, jointProductParentAug,
    rectangularWordAugCell, Category.assoc] at h ⊢
  exact h

def NativeAugmentedIso.retarget {A B D E : Aug ℙ I}
    (e : NativeAugmentedIso A B) (h : A = D) (k : B = E) : NativeAugmentedIso D E := h ▸ k ▸ e

theorem NativeAugmentedIso.retarget_hom {A B D E : Aug ℙ I}
    (e : NativeAugmentedIso A B) (h : A = D) (k : B = E) : HEq (e.retarget h k).hom e.hom := by
  subst D
  subst E
  rfl

noncomputable def NativeAugmentedIso.ident (A : Aug ℙ I) : NativeAugmentedIso A A where
  hom := AugHom.ident A
  inv := AugHom.ident A
  hom_inv := AugHom.ident_comp _
  inv_hom := AugHom.ident_comp _

noncomputable def NativeAugmentedIso.trans {A B D : Aug ℙ I}
    (e : NativeAugmentedIso A B) (f : NativeAugmentedIso B D) : NativeAugmentedIso A D where
  hom := e.hom.comp f.hom
  inv := f.inv.comp e.inv
  hom_inv := by
    rw [AugHom.comp_assoc, ← AugHom.comp_assoc f.hom, f.hom_inv, AugHom.ident_comp, e.hom_inv]
  inv_hom := by
    rw [AugHom.comp_assoc, ← AugHom.comp_assoc e.inv, e.inv_hom, AugHom.ident_comp, f.inv_hom]

theorem augmentHom_heq_native_of_eq {A B D E : Aug ℙ I}
    (p : AugHom ℙ A B) (q : AugHom ℙ D E) (h : A = D) (k : B = E)
    (e : HEq p.native q.native) : HEq p q := by
  subst D
  subst E
  exact heq_of_eq (AugHom.ext (eq_of_heq e))

theorem NativeAugmentedIso.retarget_square
    {A B D E A' B' D' E' : Aug ℙ I}
    (a : A = A') (b : B = B') (d : D = D') (e : E = E')
    (x : NativeAugmentedIso A D) (y : NativeAugmentedIso B E)
    (p : AugHom ℙ A B) (q : AugHom ℙ D E) (p' : AugHom ℙ A' B') (q' : AugHom ℙ D' E')
    (hp : HEq p p') (hq : HEq q q') (s : p.comp y.hom = x.hom.comp q) :
    p'.comp (y.retarget b e).hom = (x.retarget a d).hom.comp q' := by
  subst A'
  subst B'
  subst D'
  subst E'
  cases hp
  cases hq
  exact s

set_option backward.isDefEq.respectTransparency false in
noncomputable def binaryProductAugIso
    (N : GridBinary (symmetricCross (C:=C)) R L) (NR : GatherOuterNat R) (NL : GatherLeftNat L)
    (m : Middle T I) (mi : MiddleInv m) (h : MedialLinear m R L) (j : MedialInner m R L)
    (unit_middle : m.cell I I I I ≫ unitCollapse R J = unitCollapse R J)
    [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
    (hl : ∀ a : C, SameLeftGather T a L) (hr : ∀ b : C, SameRightGather R b)
    (hn : (fourOccurrenceExpr xs ys us vs).leaves.Nodup) :
    NativeAugmentedIso
      (independentAug R L (J.ρ I) (dependentWordAug R L J xs us V A (indexedAugmentation δ) ε)
        (dependentWordAug R L J ys vs P B (indexedAugmentation η) γ))
      (dependentWordAug R L J (xs.product ys) (crossChildWord us vs)
        (crossLabel T V P) (crossChildLabel T A B)
        (indexedAugmentation (fun z => rectangularWordAugCell R L (J.ρ I) (A z.1) (B z.2)
          (us z.1) (vs z.2) (δ z.1) (η z.2)))
        (rectangularWordAugCell R L (J.ρ I) V P xs ys ε γ)) :=
  (binaryNativeAugIso xs ys us vs V P A B R L N NR NL J m (indexedAugmentation δ)
    (indexedAugmentation η) ε γ mi hn h j unit_middle).retarget
      (separateProductAug_eq R L J xs ys us vs V P A B δ η ε γ hl hr).symm
      (jointProductAug_eq R L J xs ys us vs V P A B δ η ε γ hl hr).symm

theorem NativeAugmentedIso.retarget_addr {A B D E : Aug ℙ I}
    (e : NativeAugmentedIso A B) (h : A = D) (k : B = E) (i : Fin D.base.n) :
    (e.retarget h k).hom.native.addr i =
      Fin.cast (congrArg (fun a : Aug ℙ I => a.base.n) k)
        (e.hom.native.addr (Fin.cast (congrArg (fun a : Aug ℙ I => a.base.n) h.symm) i)) := by
  subst D
  subst E
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1400000 in
theorem binaryProductAugIso_addr
    (N : GridBinary (symmetricCross (C:=C)) R L) (NR : GatherOuterNat R) (NL : GatherLeftNat L)
    (m : Middle T I) (mi : MiddleInv m) (h : MedialLinear m R L) (j : MedialInner m R L)
    (unit_middle : m.cell I I I I ≫ unitCollapse R J = unitCollapse R J)
    [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
    (hl : ∀ a : C, SameLeftGather T a L) (hr : ∀ b : C, SameRightGather R b)
    (hn : (fourOccurrenceExpr xs ys us vs).leaves.Nodup)
    (i : Fin (independentWord
      (wordFamily (dependentLabels (T:=T) V A) (dependentWord xs us))
      (wordFamily (dependentLabels (T:=T) P B) (dependentWord ys vs))).length) :
    let e := binaryProductAugIso R L J xs ys us vs V P A B δ η ε γ N NR NL m mi h j unit_middle hl hr hn
    jointPairRetag ((dependentWord (xs.product ys) (crossChildWord us vs))[e.hom.native.addr i]) =
      quadRead (dependentWord xs us) (dependentWord ys vs)
        ((independentWord (wordFamily (dependentLabels (T:=T) V A) (dependentWord xs us))
          (wordFamily (dependentLabels (T:=T) P B) (dependentWord ys vs)))[i]) := by
  intro e
  let s := (fourOccurrenceExpr xs ys us vs).leaves
  let t := (fourJointExpr xs ys us vs).leaves
  let x := dependentWord xs us
  let y := dependentWord ys vs
  let z := dependentWord (xs.product ys) (crossChildWord us vs)
  let F := wordFamily (dependentLabels (T:=T) V A) x
  let G := wordFamily (dependentLabels (T:=T) P B) y
  let u := independentWord F G
  let r := quadRead x y
  let es := quadRead_word xs ys us vs
  let et := jointPairRetag_word xs ys us vs
  let castS := (List.length_map r).symm.trans (congrArg List.length es)
  let castT := (List.length_map (jointPairRetag : ((X × Y) × (U × W)) → _)).symm.trans (congrArg List.length et)
  let p := gridOrder (fourExchangeChart xs ys us vs)
  let v := wordEquiv p.perm hn (Fin.cast castS i)
  have re : e.hom.native.addr i = Fin.cast castT.symm v := by
    unfold e binaryProductAugIso
    rw [NativeAugmentedIso.retarget_addr]
    rfl
  change jointPairRetag z[e.hom.native.addr i] = r u[i]
  rw [re]
  have k := retag_word_get jointPairRetag z et (Fin.cast castT.symm v)
  have q := retag_word_get r u es i
  have v' : Fin.cast castT (Fin.cast castT.symm v) = v := by apply Fin.ext; rfl
  change jointPairRetag z[Fin.cast castT.symm v] = t[Fin.cast castT (Fin.cast castT.symm v)] at k
  exact k.trans ((congrArg (fun i : Fin t.length => t[i]) v').trans
    ((wordEquiv_get p.perm hn (Fin.cast castS i)).trans q.symm))

end BinaryObject
end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
