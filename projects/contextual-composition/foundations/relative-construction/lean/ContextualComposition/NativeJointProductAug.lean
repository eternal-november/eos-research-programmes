module
public import ContextualComposition.NativeJointProductBridge
@[expose] public section

/-! Product augmentation on the actual independently constructed joint input. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v w z
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)

set_option backward.isDefEq.respectTransparency false in
theorem gather_unit_collapse_flat {T : Bi (coeff (C:=C))} {I : C}
    (R : Gather 𝒮 T Zₐ) (J : UnitCompat R I)
    {X : Type u} (A : X → C) (xs : List X)
    (p : fold 𝒮 Zₐ A xs ⟶ T.obj I I) :
    DependentFibre.gather R A (T.obj I I) xs ≫ T.map p (𝟙 (T.obj I I)) ≫ unitCollapse R J =
      act 𝒮 Zₐ (fun x => T.map (𝟙 (A x)) (J.ρ I) ≫ J.ρ (A x)) xs ≫ p ≫ J.ρ I := by
  let q := J.ρ I
  let k := T.obj I I
  let f := fun x => T.map (𝟙 (A x)) q
  let H := fold 𝒮 Zₐ A xs
  have h₁ : T.map p (𝟙 k) ≫ T.map q q = T.map (p ≫ q) q := by
    have h := T.map_seq p q (𝟙 k) q
    change T.map (p ≫ q) (𝟙 k ≫ q) = _ at h
    rw [Category.id_comp] at h
    exact h.symm
  have h₂ : T.map (p ≫ q) q = T.map (𝟙 H) q ≫ T.map (p ≫ q) (𝟙 I) := by
    have h := T.map_seq (𝟙 H) (p ≫ q) q (𝟙 I)
    change T.map (𝟙 H ≫ p ≫ q) (q ≫ 𝟙 I) = _ at h
    rw [Category.id_comp, Category.comp_id] at h
    exact h
  have h₃ : T.map (p ≫ q) (𝟙 I) ≫ J.ρ I = J.ρ H ≫ p ≫ q :=
    J.natural (p ≫ q)
  have h₄ : DependentFibre.gather R A k xs ≫ T.map (𝟙 H) q =
      act 𝒮 Zₐ f xs ≫ DependentFibre.gather R A I xs :=
    gather_nat R A q xs
  have h₅ : DependentFibre.gather R A I xs ≫ J.ρ H = act 𝒮 Zₐ (fun x => J.ρ (A x)) xs :=
    gather_unit J A xs
  have h₆ : act 𝒮 Zₐ f xs ≫ act 𝒮 Zₐ (fun x => J.ρ (A x)) xs =
      act 𝒮 Zₐ (fun x => f x ≫ J.ρ (A x)) xs :=
    act_seq 𝒮 Zₐ f (fun x => J.ρ (A x)) xs
  change DependentFibre.gather R A k xs ≫ T.map p (𝟙 k) ≫ T.map q q ≫ q = _
  rw [reassoc_of% h₁, h₂]
  simp only [Category.assoc]
  rw [h₃, reassoc_of% h₄, reassoc_of% h₅, reassoc_of% h₆]

set_option backward.isDefEq.respectTransparency false in
theorem wordAug_read_eq {X : Type w} {Y : Type z} {I : C} (A : Y → C) (f : X → Y)
    (xs : List X) (ys : List Y) (h : xs.map f = ys)
    (p : fold 𝒮 Zₐ (A ∘ f) xs ⟶ I) (q : fold 𝒮 Zₐ A ys ⟶ I)
    (e : HEq p q) :
    wordAug (A ∘ f) xs p = wordAug A ys q := by
  let G := wordFamily (A ∘ f) xs
  let H := wordFamily A ys
  let c := wordTotalPin (A ∘ f) xs
  let d := wordTotalPin A ys
  rw [wordAug_total, wordAug_total]
  change totalAug G (eqToHom c ≫ p) = totalAug H (eqToHom d ≫ q)
  have K {G H : Family C} (a : G = H) (p : totalFold G ⟶ I) (q : totalFold H ⟶ I)
      (z : HEq p q) : totalAug G p = totalAug H q := by
    subst H
    exact congrArg (totalAug G) (eq_of_heq z)
  exact K (wordFamily_read_eq A f xs ys h) _ _
    ((hom_source_pin_heq c p).trans (e.trans (hom_source_pin_heq d q).symm))

section Aug
variable {T : Bi (coeff (C:=C))} {I : C}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (J : UnitCompat R I)
variable {X U Y W : Type u}
variable (xs : List X) (ys : List Y) (us : X → List U) (vs : Y → List W)
variable (V : X → C) (P : Y → C) (A : X → U → C) (B : Y → W → C)
variable (δ : ∀ x, inner (S:=binary (Additive.ofBraided (C:=C)).sum) (Z:=𝟙_ C) (indexInput A us) x ⟶ I)
variable (η : ∀ y, inner (S:=binary (Additive.ofBraided (C:=C)).sum) (Z:=𝟙_ C) (indexInput B vs) y ⟶ I)
variable (ε : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) V xs ⟶ I)
variable (γ : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) P ys ⟶ I)

set_option backward.isDefEq.respectTransparency false in
theorem jointWordAug_is_jointWordCell
    : jointWordAug xs ys us vs V P A B R L J δ η ε γ =
      jointWordCell xs ys us vs V P A B R L δ η ε γ ≫ unitCollapse R J := by
  let D := jointLeafLabels (T:=T) V P A B
  let e := raw_joint_shape xs ys us vs A B (fun x u y v => T.obj (T.obj (V x) (P y)) (T.obj u v))
  let E := jointInnerCell R L V P (indexInput A us) (indexInput B vs) δ η
  let G := jointAugRow R L J V P (indexInput A us) (indexInput B vs) δ η
  let H := fun x y => T.obj (V x) (P y)
  let k := T.obj I I
  let q := J.ρ I
  let p := independentCell R L V P xs ys ε γ
  let U := rectKeep R xs ys H k
  have m : T.map p (𝟙 k) ≫ T.map q q = T.map (p ≫ q) q := by
    have h := T.map_seq p q (𝟙 k) q
    change T.map (p ≫ q) (𝟙 k ≫ q) = _ at h
    rw [Category.id_comp] at h
    exact h.symm
  have u : U ≫ T.map (p ≫ q) q ≫ q =
      actRect (S:=𝒮) (Z:=Zₐ) xs ys (fun x y => T.map (𝟙 (H x y)) q ≫ J.ρ (H x y)) ≫
        jointParentAug R L J xs ys V P ε γ :=
    rectKeep_global R J xs ys H q (p ≫ q)
  have g (x : X) (y : Y) : E x y ≫ T.map (𝟙 (H x y)) q ≫ J.ρ (H x y) = G x y := by
    let c := independentCell R L id id ((indexInput A us).terms x) ((indexInput B vs).terms y) (δ x) (η y)
    have h := T.map_seq (𝟙 (H x y)) (𝟙 (H x y)) c q
    change T.map (𝟙 _ ≫ 𝟙 _) (c ≫ q) = T.map (𝟙 _) c ≫ T.map (𝟙 _) q at h
    rw [Category.id_comp] at h
    unfold E G jointInnerCell jointAugRow jointContAug
    change _ = _
    simp only [Category.assoc]
    rw [← reassoc_of% h]
  let p₁ := fun x y => T.map (𝟙 (H x y)) q ≫ J.ρ (H x y)
  have step : actRect (S:=𝒮) (Z:=Zₐ) xs ys E ≫ actRect (S:=𝒮) (Z:=Zₐ) xs ys p₁ =
      actRect (S:=𝒮) (Z:=Zₐ) xs ys G := by
    have w := actRect_seq (S:=𝒮) (Z:=Zₐ) xs ys E p₁
    exact w.trans (congrArg (actRect (S:=𝒮) (Z:=Zₐ) xs ys) (funext fun x => funext fun y => g x y))
  have t : actRect (S:=𝒮) (Z:=Zₐ) xs ys E ≫
      jointOuterCell (b:=I) (d:=I) R L xs ys V P ε γ ≫ unitCollapse R J =
    actRect (S:=𝒮) (Z:=Zₐ) xs ys G ≫ jointParentAug R L J xs ys V P ε γ := by
    have hu : jointOuterCell (b:=I) (d:=I) R L xs ys V P ε γ = U ≫ T.map p (𝟙 k) := by
      unfold U rectKeep jointOuterCell
      exact (Category.assoc _ _ _).symm
    rw [hu]
    change actRect (S:=𝒮) (Z:=Zₐ) xs ys E ≫ (U ≫ T.map p (𝟙 k)) ≫ (T.map q q ≫ q) = _
    simp only [Category.assoc]
    rw [reassoc_of% m, u, reassoc_of% step]
  unfold jointWordAug jointWordCell
  simp only [Category.assoc]
  exact congrArg (fun p => compressGrid D (fourJointExpr xs ys us vs) ≫ eqToHom e ≫ p) t.symm

def jointProductChildAug (x : X × Y) :
    fold 𝒮 Zₐ (crossChildLabel T A B x) (crossChildWord us vs x) ⟶ I :=
  jointIndexedChildCell R L us vs A B δ η x ≫ J.ρ I

def jointProductParentAug : fold 𝒮 Zₐ (crossLabel T V P) (xs.product ys) ⟶ I :=
  (rectWordChart (crossLabel T V P) xs ys ≫ independentCell R L V P xs ys ε γ) ≫ J.ρ I

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1400000 in
/-- The original joint augmentation and the independently constructed
product followed by accumulation have exactly the same global map. -/
theorem jointWordAug_product_heq
    [lF : ∀ a : C, (leftFactor T a).LaxBraided]
    [rF : (rightFactor (T:=T) (T.obj I I)).LaxBraided]
    (hl : ∀ a : C, SameLeftGather T a L) (hr : SameRightGather R (T.obj I I)) :
    let V₀ := crossLabel T V P
    let A₀ := crossChildLabel T A B
    let ps := xs.product ys
    let cs := crossChildWord us vs
    HEq
      (dependentWordAugCell R L J ps cs V₀ A₀
        (fun x => eqToHom (std_fold_map id (A₀ x) (cs x)) ≫ jointProductChildAug R L J us vs A B δ η x)
        (jointProductParentAug R L J xs ys V P ε γ))
      (jointWordAug xs ys us vs V P A B R L J δ η ε γ) := by
  intro V₀ A₀ ps cs
  let F := dependentLabels (T:=T) V₀ A₀
  let G := jointLeafLabels (T:=T) V P A B
  let k := T.obj I I
  let d := jointIndexedChildCell R L us vs A B δ η
  let p := rectWordChart V₀ xs ys ≫ independentCell R L V P xs ys ε γ
  let h := fun x => (Lin.left L (V₀ x)).collect (A₀ x) (cs x) ≫ T.map (𝟙 (V₀ x)) (d x)
  let r := fun x => T.map (𝟙 (V₀ x)) (J.ρ I) ≫ J.ρ (V₀ x)
  let q := J.ρ I
  let e := fun x => (Lin.left L (V₀ x)).collect (A₀ x) (cs x) ≫
    T.map (𝟙 (V₀ x)) (jointProductChildAug R L J us vs A B δ η x) ≫ J.ρ (V₀ x)
  have ee (x : X × Y) : h x ≫ r x = e x := by
    let H := leftFactor T (V₀ x)
    change ((Lin.left L (V₀ x)).collect (A₀ x) (cs x) ≫ H.map (d x)) ≫
      H.map q ≫ J.ρ (V₀ x) = (Lin.left L (V₀ x)).collect (A₀ x) (cs x) ≫ H.map (d x ≫ q) ≫ J.ρ (V₀ x)
    rw [H.map_comp]
    simp only [Category.assoc]
  have ss : act 𝒮 Zₐ h ps ≫ act 𝒮 Zₐ r ps = act 𝒮 Zₐ e ps :=
    (act_seq 𝒮 Zₐ h r ps).trans (congrArg (fun q => act 𝒮 Zₐ q ps) (funext ee))
  have h₀ := dependentWordAug_raw_rows R L J ps cs V₀ A₀
    (jointProductChildAug R L J us vs A B δ η) (jointProductParentAug R L J xs ys V P ε γ)
  have h₁ := jointWordCell_flat R L xs ys us vs V P A B δ η ε γ hl hr
  have h₂ := gather_unit_collapse_flat R J V₀ ps p
  rw [h₀, jointWordAug_is_jointWordCell, h₁]
  simp only [Category.assoc]
  change HEq
    (taggedRaggedRows F (fun x y => (x,y)) cs ps ≫ act 𝒮 Zₐ e ps ≫ p ≫ q)
    (eqToHom (congrArg (fold 𝒮 Zₐ G) (fourJointExpr_rect_word xs ys us vs)) ≫
      taggedRaggedRows G jointInnerTag cs ps ≫ act 𝒮 Zₐ h ps ≫
        DependentFibre.gather R V₀ k ps ≫ T.map p (𝟙 k) ≫ unitCollapse R J)
  rw [h₂, reassoc_of% ss]
  apply HEq.trans _ (hom_source_pin_heq _ _).symm
  let l₀ := ps.flatMap (fun x => (cs x).map (fun y => (x,y)))
  let l₁ := ps.flatMap (fun x => (cs x).map (jointInnerTag x))
  have z : l₀.map jointPairRetag = l₁ := by
    simp only [l₀, l₁, List.map_flatMap, List.map_map]
    rfl
  exact structural_seq_heq (K:=coeff (C:=C))
    ((std_fold_map G jointPairRetag l₀).symm.trans (congrArg (fold 𝒮 Zₐ G) z))
    (rfl : fold 𝒮 Zₐ (fun x => fold 𝒮 Zₐ (G ∘ jointInnerTag x) (cs x)) ps = _)
    (rfl : I = _) (taggedRaggedRows_tag_heq G jointPairRetag Prod.mk cs ps) HEq.rfl

set_option backward.isDefEq.respectTransparency false in
/-- The whole output augmented object is the same, not just its
terminal-cell coefficient, after the literal raw presentation read. -/
theorem jointDependentWordAug_eq
    [lF : ∀ a : C, (leftFactor T a).LaxBraided]
    [rF : (rightFactor (T:=T) (T.obj I I)).LaxBraided]
    (hl : ∀ a : C, SameLeftGather T a L) (hr : SameRightGather R (T.obj I I)) :
    let V₀ := crossLabel T V P
    let A₀ := crossChildLabel T A B
    let ps := xs.product ys
    let cs := crossChildWord us vs
    dependentWordAug R L J ps cs V₀ A₀
      (fun x => eqToHom (std_fold_map id (A₀ x) (cs x)) ≫ jointProductChildAug R L J us vs A B δ η x)
      (jointProductParentAug R L J xs ys V P ε γ) =
    wordAug (jointLeafLabels (T:=T) V P A B) (fourJointExpr xs ys us vs).leaves
      (jointWordAug xs ys us vs V P A B R L J δ η ε γ) := by
  intro V₀ A₀ ps cs
  exact wordAug_read_eq (jointLeafLabels (T:=T) V P A B) jointPairRetag
    (dependentWord ps cs) (fourJointExpr xs ys us vs).leaves (jointPairRetag_word xs ys us vs) _ _
    (jointWordAug_product_heq R L J xs ys us vs V P A B δ η ε γ hl hr)

end Aug
end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
