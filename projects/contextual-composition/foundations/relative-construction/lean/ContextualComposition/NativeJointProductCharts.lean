module
public import ContextualComposition.NativeJointProductInput
@[expose] public section

/-! Exact rectangular and ragged chart changes for the original binary joint coefficient cell. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)

variable {T : Bi (coeff (C:=C))}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))

set_option backward.isDefEq.respectTransparency false in
/-- Flatten one layer of an actual rectangular gather for a fixed factor.
The two nullary gathers are retained by the tree comparison. -/
theorem collect_rectWord (F : C ⥤ C) [F.LaxMonoidal] {X Y : Type u}
    (A : X × Y → C) (xs : List X) (ys : List Y) :
    let K := linearFunctor F
    let B := fun x => fold 𝒮 Zₐ (fun y => A (x,y)) ys
    rectWordChart (fun t => F.obj (A t)) xs ys ≫
      act 𝒮 Zₐ (fun x => K.collect (fun y => A (x,y)) ys) xs ≫ K.collect B xs =
    K.collect A (xs.product ys) ≫ F.map (rectWordChart A xs ys) := by
  intro K B
  let e := rectPairExpr xs ys
  let W := fun t => F.obj (A t)
  let a := rectPairExpr_eval A xs ys
  let b := rectPairExpr_eval W xs ys
  let c := rectPairExpr_leaves xs ys
  let k := fun x => K.collect (fun y => A (x,y)) ys
  let p := K.collect B xs
  let G := GridExpr.gatherE K A e
  have hg : G ≫ eqToHom (congrArg F.obj a) = eqToHom b ≫ (act 𝒮 Zₐ k xs ≫ p) :=
    heq_paste b (congrArg F.obj a) (gatherE_over_nested_heq K A (fun x y => (x,y)) (fun _ => ys) xs)
  have hc := collect_compressGrid F A e
  have h₀ := rectPairExpr_chart W xs ys
  have h₁ := rectPairExpr_chart A xs ys
  have hf' {x y : C} (p : x = y) : eqToHom (congrArg F.obj p) = F.map (eqToHom p) := by
    subst y
    simp only [eqToHom_refl, F.map_id]
  have hf := hf' a
  have Hd {l l' : List (X × Y)} (eq : l = l') :
      K.collect A l ≫ F.map (eqToHom (congrArg (fold 𝒮 Zₐ A) eq)) =
        eqToHom (congrArg (fold 𝒮 Zₐ W) eq) ≫ K.collect A l' := by
    subst l'
    let h : fold 𝒮 Zₐ W l ⟶ F.obj (fold 𝒮 Zₐ A l) := K.collect A l
    change h ≫ F.map (eqToHom (rfl : fold 𝒮 Zₐ A l = _)) =
      eqToHom (rfl : fold 𝒮 Zₐ W l = _) ≫ h
    simp only [eqToHom_refl, F.map_id, Category.comp_id, Category.id_comp]
  have hd := Hd c
  let h := congrArg (fun r => compressGrid W e ≫ r) hg
  change compressGrid W e ≫ G ≫ eqToHom (congrArg F.obj a) =
    compressGrid W e ≫ eqToHom b ≫ act 𝒮 Zₐ k xs ≫ p at h
  rw [reassoc_of% h₀, reassoc_of% hc, hf, ← F.map_comp, h₁, F.map_comp, ← Category.assoc (K.collect A e.leaves), hd] at h
  simp only [Category.assoc] at h
  exact (cancel_epi (eqToHom (congrArg (fold 𝒮 Zₐ W) c))).mp h.symm

set_option backward.isDefEq.respectTransparency false in
theorem rightGather_rectWord (R : Gather 𝒮 T Zₐ) (b : C)
    [(rightFactor (T:=T) b).LaxBraided] (hr : SameRightGather R b)
    {X Y : Type u} (A : X × Y → C) (xs : List X) (ys : List Y) :
    rectWordChart (fun t => T.obj (A t) b) xs ys ≫
      act 𝒮 Zₐ (fun x => DependentFibre.gather R (fun y => A (x,y)) b ys) xs ≫
        DependentFibre.gather R (fun x => fold 𝒮 Zₐ (fun y => A (x,y)) ys) b xs =
    DependentFibre.gather R A b (xs.product ys) ≫ T.map (rectWordChart A xs ys) (𝟙 b) := by
  simpa only [rightFactor_sameCollect R hr] using collect_rectWord (rightFactor (T:=T) b) A xs ys

set_option backward.isDefEq.respectTransparency false in
theorem leftGather_rectWord (L : LeftGather 𝒮 T Zₐ) (a : C)
    [(leftFactor T a).LaxBraided] (hl : SameLeftGather T a L)
    {X Y : Type u} (A : X × Y → C) (xs : List X) (ys : List Y) :
    rectWordChart (fun t => T.obj a (A t)) xs ys ≫
      act 𝒮 Zₐ (fun x => (Lin.left L a).collect (fun y => A (x,y)) ys) xs ≫
        (Lin.left L a).collect (fun x => fold 𝒮 Zₐ (fun y => A (x,y)) ys) xs =
    (Lin.left L a).collect A (xs.product ys) ≫ T.map (𝟙 a) (rectWordChart A xs ys) := by
  simpa only [leftFactor_sameCollect T a L hl] using collect_rectWord (leftFactor T a) A xs ys

theorem linRight_collect_gather (R : Gather 𝒮 T Zₐ) (b : C)
    {X : Type u} (A : X → C) (xs : List X) :
    (Lin.right R b).collect A xs = DependentFibre.gather R A b xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [Lin.collect, DependentFibre.gather, ih]

set_option backward.isDefEq.respectTransparency false in
theorem jointOuterCell_flat_chart (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    {X Y : Type u} (xs : List X) (ys : List Y) (V : X → C) (W : Y → C)
    {a b c d : C} (α : fold 𝒮 Zₐ V xs ⟶ a) (γ : fold 𝒮 Zₐ W ys ⟶ c)
    [(rightFactor (T:=T) (T.obj b d)).LaxBraided] (hr : SameRightGather R (T.obj b d)) :
    let P := crossLabel T V W
    let k := T.obj b d
    rectWordChart (fun t => T.obj (P t) k) xs ys ≫
      jointOuterCell (b:=b) (d:=d) R L xs ys V W α γ =
    DependentFibre.gather R P k (xs.product ys) ≫
      T.map (rectWordChart P xs ys ≫ independentCell R L V W xs ys α γ) (𝟙 k) := by
  intro P k
  let F := rightFactor (T:=T) k
  let B := fun x => fold 𝒮 Zₐ (fun y => P (x,y)) ys
  let q := fun x => DependentFibre.gather R (fun y => P (x,y)) k ys
  let c₀ := independentCell R L V W xs ys α γ
  have e : jointOuterCell (b:=b) (d:=d) R L xs ys V W α γ =
      act 𝒮 Zₐ q xs ≫ DependentFibre.gather R B k xs ≫ F.map c₀ := by
    unfold jointOuterCell
    simp only [linRight_collect_gather]
    rfl
  have h := rightGather_rectWord R k hr P xs ys
  change _ = DependentFibre.gather R P k (xs.product ys) ≫ F.map (rectWordChart P xs ys ≫ c₀)
  rw [e, F.map_comp, ← reassoc_of% h]

set_option backward.isDefEq.respectTransparency false in
theorem jointInnerCell_flat_chart (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    {X Y : Type u} (xs : List X) (ys : List Y) (V : X → C) (W : Y → C)
    {a b d : C} (β : fold 𝒮 Zₐ V xs ⟶ b) (θ : fold 𝒮 Zₐ W ys ⟶ d)
    [(leftFactor T a).LaxBraided] (hl : SameLeftGather T a L) :
    let P := crossLabel T V W
    let c₀ := independentCell R L V W xs ys β θ
    let H := Lin.left L a
    rectWordChart (fun t => T.obj a (P t)) xs ys ≫
      act 𝒮 Zₐ (fun x => H.collect (fun y => P (x,y)) ys) xs ≫
      H.collect (fun x => fold 𝒮 Zₐ (fun y => P (x,y)) ys) xs ≫ T.map (𝟙 a) c₀ =
    H.collect P (xs.product ys) ≫ T.map (𝟙 a) (rectWordChart P xs ys ≫ c₀) := by
  intro P c₀ H
  let F := leftFactor T a
  have h := leftGather_rectWord L a hl P xs ys
  change _ = H.collect P (xs.product ys) ≫ F.map (rectWordChart P xs ys ≫ c₀)
  rw [F.map_comp, ← reassoc_of% h]

set_option backward.isDefEq.respectTransparency false in
theorem retaggedRect_chart {Q X Y : Type u} (A : Q → C) (f : X × Y → Q)
    (xs : List X) (ys : List Y) :
    let e := rectPairExpr xs ys
    let a := retagGrid_eval A f e
    let b := rectPairExpr_eval (A ∘ f) xs ys
    let c := (retagGrid_leaves f e).trans (congrArg (List.map f) (rectPairExpr_leaves xs ys))
    compressGrid A (retagGrid f e) ≫ eqToHom (a.trans b) =
      eqToHom (congrArg (fold 𝒮 Zₐ A) c) ≫
        eqToHom (std_fold_map A f (xs.product ys)) ≫ rectWordChart (A ∘ f) xs ys := by
  intro e a b c
  have h₀ := compressGrid_retag A f e
  have h₁ := rectPairExpr_chart (A ∘ f) xs ys
  rw [← eqToHom_trans a b, ← Category.assoc, h₀]
  simp only [Category.assoc]
  rw [h₁]
  simp only [eqToHom_trans_assoc]

def jointInnerTag {X U Y W : Type u} (t : X × Y) (s : U × W) : X × U × Y × W :=
  jointPairRetag (t,s)

theorem fourJointExpr_rect {X U Y W : Type u}
    (xs : List X) (ys : List Y) (us : X → List U) (vs : Y → List W) :
    fourJointExpr xs ys us vs = GridExpr.over
      (fun x => GridExpr.over (fun y => retagGrid (jointInnerTag (x,y))
        (rectPairExpr (us x) (vs y))) ys) xs := by
  simp only [fourJointExpr, rectPairExpr, retagGrid_over, retagGrid, innerQuad]
  rfl

def jointInnerNested {X U Y W : Type u} (A : X × U × Y × W → C)
    (us : X → List U) (vs : Y → List W) (p : X × Y) : C :=
  fold 𝒮 Zₐ (fun u => fold 𝒮 Zₐ (fun v => A (p.1,u,p.2,v)) (vs p.2)) (us p.1)

theorem fourJointExpr_rect_eval {X U Y W : Type u}
    (A : X × U × Y × W → C) (xs : List X) (ys : List Y) (us : X → List U) (vs : Y → List W) :
    GridExpr.eval (S:=𝒮) (Z:=Zₐ) A (fourJointExpr xs ys us vs) =
      fold 𝒮 Zₐ (fun x => fold 𝒮 Zₐ (fun y => jointInnerNested A us vs (x,y)) ys) xs := by
  rw [fourJointExpr_rect, GridExpr.eval_over]
  apply congrArg (fun G => fold 𝒮 Zₐ G xs)
  funext x
  rw [GridExpr.eval_over]
  apply congrArg (fun G => fold 𝒮 Zₐ G ys)
  funext y
  exact (retagGrid_eval A (jointInnerTag (x,y)) _).trans
    (rectPairExpr_eval (A ∘ jointInnerTag (x,y)) (us x) (vs y))

theorem fourJointExpr_rect_word {X U Y W : Type u}
    (xs : List X) (ys : List Y) (us : X → List U) (vs : Y → List W) :
    (fourJointExpr xs ys us vs).leaves =
      (xs.product ys).flatMap (fun p => (crossChildWord us vs p).map (jointInnerTag p)) := by
  have h := jointPairRetag_word xs ys us vs
  rw [← h]
  simp only [dependentWord, List.map_flatMap, List.map_map]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
theorem fourJointExpr_flat_chart {X U Y W : Type u}
    (A : X × U × Y × W → C) (xs : List X) (ys : List Y) (us : X → List U) (vs : Y → List W)
    (D : X × Y → C) (g : ∀ p, jointInnerNested A us vs p ⟶ D p) :
    compressGrid A (fourJointExpr xs ys us vs) ≫ eqToHom (fourJointExpr_rect_eval A xs ys us vs) ≫
      actRect (S:=𝒮) (Z:=Zₐ) xs ys (fun x y => g (x,y)) =
    eqToHom (congrArg (fold 𝒮 Zₐ A) (fourJointExpr_rect_word xs ys us vs)) ≫
      taggedRaggedRows A jointInnerTag (crossChildWord us vs) (xs.product ys) ≫
      act 𝒮 Zₐ (fun p => rectWordChart (A ∘ jointInnerTag p) (us p.1) (vs p.2) ≫ g p)
        (xs.product ys) ≫ rectWordChart D xs ys := by
  let ps := xs.product ys
  let P := fun p : X × Y => retagGrid (jointInnerTag p) (rectPairExpr (us p.1) (vs p.2))
  let Q := fun x => GridExpr.over (fun y => P (x,y)) ys
  let F := fun p => GridExpr.eval (S:=𝒮) (Z:=Zₐ) A (P p)
  let B := jointInnerNested A us vs
  let a : ∀ p, F p = B p := fun p =>
    (retagGrid_eval A (jointInnerTag p) _).trans
      (rectPairExpr_eval (A ∘ jointInnerTag p) (us p.1) (vs p.2))
  let b := fun p => eqToHom (a p) ≫ g p
  let h := fourJointExpr_rect xs ys us vs
  let q := GridExpr.over Q xs
  let K := fold 𝒮 Zₐ A
  let c := fun p => ((retagGrid_leaves (jointInnerTag p) (rectPairExpr (us p.1) (vs p.2))).trans
    (congrArg (List.map (jointInnerTag p)) (rectPairExpr_leaves (us p.1) (vs p.2))))
  let e := fun p => std_fold_map A (jointInnerTag p) (crossChildWord us vs p)
  let w := fun p => rectWordChart (A ∘ jointInnerTag p) (us p.1) (vs p.2) ≫ g p
  have hr (p : X × Y) : compressGrid A (P p) ≫ b p =
      eqToHom (congrArg K (c p)) ≫ (eqToHom (e p) ≫ w p) := by
    change compressGrid A (P p) ≫ eqToHom (a p) ≫ g p = _
    rw [reassoc_of% retaggedRect_chart A (jointInnerTag p) (us p.1) (vs p.2)]
  have he (x : X) :
      act 𝒮 Zₐ (fun y => eqToHom (a (x,y))) ys = eqToHom
        (congrArg (fun G => fold 𝒮 Zₐ G ys) (funext fun y => a (x,y))) :=
    std_act_eqToHom (fun y => a (x,y)) ys
  have ha :
      actRect (S:=𝒮) (Z:=Zₐ) xs ys (fun x y => eqToHom (a (x,y))) = eqToHom
        (congrArg (fun G => fold 𝒮 Zₐ G xs)
          (funext fun x => congrArg (fun G => fold 𝒮 Zₐ G ys) (funext fun y => a (x,y)))) := by
    simp only [actRect, he, std_act_eqToHom]
  have w₀ := compressGrid_pair_context_post A P xs ys D b
  let af := congrArg (fun t : GridExpr (X × U × Y × W) => K t.leaves) h
  let ae := congrArg (GridExpr.eval (S:=𝒮) (Z:=Zₐ) A) h
  have H : compressGrid A (fourJointExpr xs ys us vs) ≫ eqToHom ae =
      eqToHom af ≫ compressGrid A q := by
    have th {p q : GridExpr (X × U × Y × W)} (h : p = q) :
        compressGrid A p ≫ eqToHom (congrArg (GridExpr.eval (S:=𝒮) (Z:=Zₐ) A) h) =
        eqToHom (congrArg (fun t => K t.leaves) h) ≫ compressGrid A q := by
      subst q
      simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
    exact th h
  let a₁ := (GridExpr.eval_over A Q xs).trans (congrArg (fun k => fold 𝒮 Zₐ k xs)
      (funext fun x => GridExpr.eval_over A (fun y => P (x,y)) ys))
  let a₂ := congrArg (fun G => fold 𝒮 Zₐ G xs)
          (funext fun x => congrArg (fun G => fold 𝒮 Zₐ G ys) (funext fun y => a (x,y)))
  rw [show fourJointExpr_rect_eval A xs ys us vs = ae.trans (a₁.trans a₂) from Subsingleton.elim _ _,
    ← eqToHom_trans ae (a₁.trans a₂), ← eqToHom_trans a₁ a₂]
  simp only [Category.assoc]
  change compressGrid A (fourJointExpr xs ys us vs) ≫
      eqToHom ae ≫ eqToHom a₁ ≫ eqToHom a₂ ≫ actRect (S:=𝒮) (Z:=Zₐ) xs ys (fun x y => g (x,y)) =
    eqToHom _ ≫ taggedRaggedRows A jointInnerTag (crossChildWord us vs) ps ≫
      act 𝒮 Zₐ w ps ≫ rectWordChart D xs ys
  rw [reassoc_of% H, ← ha]
  have comp : actRect (S:=𝒮) (Z:=Zₐ) xs ys (fun x y => eqToHom (a (x,y))) ≫
      actRect (S:=𝒮) (Z:=Zₐ) xs ys (fun x y => g (x,y)) =
      actRect (S:=𝒮) (Z:=Zₐ) xs ys (fun x y => b (x,y)) :=
    actRect_seq (S:=𝒮) (Z:=Zₐ) xs ys (fun x y => eqToHom (a (x,y))) (fun x y => g (x,y))
  rw [comp]
  have k : compressGrid A q ≫ eqToHom a₁ ≫ actRect (S:=𝒮) (Z:=Zₐ) xs ys (fun x y => b (x,y)) =
      _ := w₀
  rw [k, show (fun p => compressGrid A (P p) ≫ b p) = _ from funext hr,
    ← act_seq, ← act_seq]
  simp only [Category.assoc]
  rw [reassoc_of% rowsChart_rows_congr A c ps]
  unfold taggedRaggedRows
  simp only [Category.assoc, eqToHom_trans_assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem indexedLeftRow {T : Bi (coeff (C:=C))} (L : LeftGather 𝒮 T Zₐ)
    {Y : Type u} (a : C) (W : Y → C) (ys : List Y) {b : C}
    (p : fold 𝒮 Zₐ W ys ⟶ b) :
    eqToHom (std_fold_map (T.obj a) W ys) ≫ (Lin.left L a).collect W ys ≫ T.map (𝟙 a) p =
      gatherLeft L a (ys.map W) ≫ T.map (𝟙 a) (eqToHom (std_fold_map id W ys) ≫ p) := by
  let F := leftFactor T a
  let G := Lin.left L a
  let d := std_fold_map id W ys
  let c := std_fold_map (T.obj a) W ys
  have k : G.collect id (ys.map W) ≫ eqToHom (congrArg G.obj d) =
      eqToHom c ≫ G.collect W ys :=
    heq_paste c (congrArg G.obj d) (lin_collect_relabel G id W ys)
  have m {u v : C} (e : u = v) : F.map (eqToHom e) = eqToHom (congrArg F.obj e) := by
    subst v
    rw [eqToHom_refl, eqToHom_refl, F.map_id]
  rw [gatherLeft_eq_collect]
  change eqToHom c ≫ G.collect W ys ≫ F.map p = G.collect id (ys.map W) ≫ F.map (eqToHom d ≫ p)
  rw [F.map_comp, m d, reassoc_of% k]

theorem nestedRect_map {X Y A B : Type u} (K : A → B → C)
    (f : X → A) (g : Y → B) (xs : List X) (ys : List Y) :
    fold 𝒮 Zₐ (fun x => fold 𝒮 Zₐ (K x) (ys.map g)) (xs.map f) =
      fold 𝒮 Zₐ (fun x => fold 𝒮 Zₐ (K (f x) ∘ g) ys) xs :=
  (std_fold_map (fun x => fold 𝒮 Zₐ (K x) (ys.map g)) f xs).trans
    (congrArg (fun H => fold 𝒮 Zₐ H xs) (funext fun x => std_fold_map (K (f x)) g ys))

set_option backward.isDefEq.respectTransparency false in
theorem independentCell_indexed_heq (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    {X Y : Type u} (A : X → C) (B : Y → C) (xs : List X) (ys : List Y)
    {b d : C} (p : fold 𝒮 Zₐ id (xs.map A) ⟶ b) (q : fold 𝒮 Zₐ id (ys.map B) ⟶ d) :
    HEq (independentCell R L A B xs ys
          (eqToHom (std_fold_map id A xs).symm ≫ p) (eqToHom (std_fold_map id B ys).symm ≫ q))
      (independentCell R L id id (xs.map A) (ys.map B) p q) := by
  let h := rowGather_map_heq R L id id A B xs ys
  let a := (std_fold_map id A xs).symm
  let c := (std_fold_map id B ys).symm
  exact structural_seq_heq (K:=coeff (C:=C))
    (nestedRect_map T.obj A B xs ys).symm (congrArg₂ T.obj a c) rfl h
    (biMap_heq (T:=T) a rfl c rfl (hom_source_pin_heq a p) (hom_source_pin_heq c q))

set_option backward.isDefEq.respectTransparency false in
theorem jointInnerValue_indexed_heq (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    {X Y : Type u} (A : X → C) (B : Y → C) (xs : List X) (ys : List Y)
    {a b d : C} (p : fold 𝒮 Zₐ id (xs.map A) ⟶ b) (q : fold 𝒮 Zₐ id (ys.map B) ⟶ d) :
    let F := Lin.left L a
    let J := fun x y => T.obj (A x) (B y)
    HEq
      (act 𝒮 Zₐ (fun x => F.collect (J x) ys) xs ≫
        F.collect (fun x => fold 𝒮 Zₐ (J x) ys) xs ≫
        T.map (𝟙 a) (independentCell R L A B xs ys
          (eqToHom (std_fold_map id A xs).symm ≫ p) (eqToHom (std_fold_map id B ys).symm ≫ q)))
      (act 𝒮 Zₐ (fun x => F.collect (T.obj x) (ys.map B)) (xs.map A) ≫
        F.collect (fun x => fold 𝒮 Zₐ (T.obj x) (ys.map B)) (xs.map A) ≫
        T.map (𝟙 a) (independentCell R L id id (xs.map A) (ys.map B) p q)) := by
  intro F J
  let G := fun x => fold 𝒮 Zₐ (T.obj x) (ys.map B)
  let k := fun x => F.collect (J x) ys
  let j := fun x => F.collect (T.obj (A x)) (ys.map B)
  let d₂ := (std_fold_map G A xs).symm
  let a₂ := (std_fold_map (fun x => fold 𝒮 Zₐ (fun y => T.obj a (T.obj x y)) (ys.map B)) A xs).symm
  have first : HEq
      (act 𝒮 Zₐ k xs ≫ F.collect (fun x => fold 𝒮 Zₐ (J x) ys) xs)
      (act 𝒮 Zₐ j xs ≫ F.collect (G ∘ A) xs) :=
    linCollect_rows_map_heq F (fun x => T.obj (A x)) (fun _ => B) (fun _ => ys) xs
  have second : HEq
      (act 𝒮 Zₐ j xs ≫ F.collect (G ∘ A) xs)
      (act 𝒮 Zₐ (fun x => F.collect (T.obj x) (ys.map B)) (xs.map A) ≫ F.collect G (xs.map A)) :=
    structural_seq_heq (K:=coeff (C:=C)) a₂
      ((std_fold_map (fun z => T.obj a (G z)) A xs).symm) (congrArg (T.obj a) d₂)
      (actRetag_heq
        (A:=fun x => fold 𝒮 Zₐ (fun y => T.obj a (T.obj x y)) (ys.map B))
        (B:=fun x => T.obj a (G x)) A (fun x => F.collect (T.obj x) (ys.map B)) xs) (linCollect_map_heq F G A xs)
  let e := (nestedRect_map T.obj A B xs ys).symm
  let e' := (nestedRect_map (fun x y => T.obj a (T.obj x y)) A B xs ys).symm
  have hmap : HEq (T.map (𝟙 a) (independentCell R L A B xs ys
      (eqToHom (std_fold_map id A xs).symm ≫ p) (eqToHom (std_fold_map id B ys).symm ≫ q)))
      (T.map (𝟙 a) (independentCell R L id id (xs.map A) (ys.map B) p q)) :=
    biMap_heq (T:=T) rfl rfl e rfl (show HEq (𝟙 a) (𝟙 a) from HEq.rfl)
      (independentCell_indexed_heq R L A B xs ys p q)
  have h := structural_seq_heq (K:=coeff (C:=C)) e' (congrArg (T.obj a) e)
    (rfl : T.obj a (T.obj b d) = _) (first.trans second) hmap
  simpa only [Category.assoc] using h

section ActualJoint
variable {X U Y W : Type u}
variable (xs : List X) (ys : List Y) (us : X → List U) (vs : Y → List W)
variable (V : X → C) (P : Y → C) (A : X → U → C) (B : Y → W → C)
variable {a b c d : C}
variable (β : ∀ x, inner (S:=binary (Additive.ofBraided (C:=C)).sum) (Z:=𝟙_ C) (indexInput A us) x ⟶ b)
variable (θ : ∀ y, inner (S:=binary (Additive.ofBraided (C:=C)).sum) (Z:=𝟙_ C) (indexInput B vs) y ⟶ d)
variable (α : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) V xs ⟶ a)
variable (γ : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) P ys ⟶ c)

def jointIndexedChildCell (x : X × Y) :
    fold 𝒮 Zₐ (crossChildLabel T A B x) (crossChildWord us vs x) ⟶ T.obj b d :=
  rectWordChart (crossChildLabel T A B x) (us x.1) (vs x.2) ≫
    independentCell R L (A x.1) (B x.2) (us x.1) (vs x.2)
      (eqToHom (std_fold_map id (A x.1) (us x.1)).symm ≫ β x.1)
      (eqToHom (std_fold_map id (B x.2) (vs x.2)).symm ≫ θ x.2)

def jointIndexedInner (x : X × Y) :
    jointInnerNested (jointLeafLabels (T:=T) V P A B) us vs x ⟶ T.obj (crossLabel T V P x) (T.obj b d) :=
  let p := crossLabel T V P x
  let F := Lin.left L p
  let K := fun u v => T.obj (A x.1 u) (B x.2 v)
  act 𝒮 Zₐ (fun u => F.collect (K u) (vs x.2)) (us x.1) ≫
    F.collect (fun u => fold 𝒮 Zₐ (K u) (vs x.2)) (us x.1) ≫
    T.map (𝟙 p) (independentCell R L (A x.1) (B x.2) (us x.1) (vs x.2)
      (eqToHom (std_fold_map id (A x.1) (us x.1)).symm ≫ β x.1)
      (eqToHom (std_fold_map id (B x.2) (vs x.2)).symm ≫ θ x.2))

set_option backward.isDefEq.respectTransparency false in
theorem jointIndexedInner_agrees (x : X × Y) :
    let e := nestedRect_map (fun u v => T.obj (crossLabel T V P x) (T.obj u v))
      (A x.1) (B x.2) (us x.1) (vs x.2)
    jointInnerCell R L V P (indexInput A us) (indexInput B vs) β θ x.1 x.2 =
      eqToHom e ≫ jointIndexedInner R L us vs V P A B β θ x := by
  intro e
  have h := jointInnerValue_indexed_heq R L (A x.1) (B x.2) (us x.1) (vs x.2)
    (a:=crossLabel T V P x) (β x.1) (θ x.2)
  have h' := heq_paste e (rfl : T.obj (crossLabel T V P x) (T.obj b d) = _) h.symm
  rw [eqToHom_refl, Category.comp_id] at h'
  exact h'

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1300000 in
theorem jointWordCell_flat
    [lF : ∀ p : C, (leftFactor T p).LaxBraided] [rF : (rightFactor (T:=T) (T.obj b d)).LaxBraided]
    (hl : ∀ p : C, SameLeftGather T p L) (hr : SameRightGather R (T.obj b d)) :
    let K := jointLeafLabels (T:=T) V P A B
    let ps := xs.product ys
    let cs := crossChildWord us vs
    let H := crossLabel T V P
    let child := crossChildLabel T A B
    let k := T.obj b d
    jointWordCell xs ys us vs V P A B R L β θ α γ =
      eqToHom (congrArg (fold 𝒮 Zₐ K) (fourJointExpr_rect_word xs ys us vs)) ≫
        taggedRaggedRows K jointInnerTag cs ps ≫
        act 𝒮 Zₐ (fun x => (Lin.left L (H x)).collect (child x) (cs x) ≫
          T.map (𝟙 (H x)) (jointIndexedChildCell R L us vs A B β θ x)) ps ≫
        DependentFibre.gather R H k ps ≫
        T.map (rectWordChart H xs ys ≫ independentCell R L V P xs ys α γ) (𝟙 k) := by
  intro K ps cs H child k
  let e := fun (x : X × Y) => nestedRect_map (fun u v => T.obj (H x) (T.obj u v))
    (A x.1) (B x.2) (us x.1) (vs x.2)
  let F := fun (x : X × Y) => T.obj (H x) k
  let g := jointIndexedInner R L us vs V P A B β θ
  let c₀ := jointOuterCell (b:=b) (d:=d) R L xs ys V P α γ
  let p := fourJointExpr_rect_eval K xs ys us vs
  let q := raw_joint_shape xs ys us vs A B (fun x u y v => T.obj (T.obj (V x) (P y)) (T.obj u v))
  have r (x : X) :
      act 𝒮 Zₐ (fun y => eqToHom (e (x,y))) ys =
        eqToHom (congrArg (fun f => fold 𝒮 Zₐ f ys) (funext fun y => e (x,y))) :=
    std_act_eqToHom (fun y => e (x,y)) ys
  let z := congrArg (fun f => fold 𝒮 Zₐ f xs)
    (funext fun x => congrArg (fun f => fold 𝒮 Zₐ f ys) (funext fun y => e (x,y)))
  have rr : actRect (S:=𝒮) (Z:=Zₐ) xs ys (fun x y => eqToHom (e (x,y))) = eqToHom z := by
    simp only [actRect, r, std_act_eqToHom]
  have hp : eqToHom q ≫ eqToHom z = eqToHom p := by rw [eqToHom_trans]
  have h₁ := fourJointExpr_flat_chart K xs ys us vs F g
  have h₂ := jointOuterCell_flat_chart R L xs ys V P (b:=b) (d:=d) α γ hr
  have h₃ (x : X × Y) :
      rectWordChart (K ∘ jointInnerTag x) (us x.1) (vs x.2) ≫ g x =
        (Lin.left L (H x)).collect (child x) (cs x) ≫
          T.map (𝟙 (H x)) (jointIndexedChildCell R L us vs A B β θ x) :=
    jointInnerCell_flat_chart R L (us x.1) (vs x.2) (A x.1) (B x.2)
      (eqToHom (std_fold_map id (A x.1) (us x.1)).symm ≫ β x.1)
      (eqToHom (std_fold_map id (B x.2) (vs x.2)).symm ≫ θ x.2) (hl (H x))
  change compressGrid K (fourJointExpr xs ys us vs) ≫ eqToHom q ≫
    actRect (S:=𝒮) (Z:=Zₐ) xs ys (jointInnerCell R L V P (indexInput A us) (indexInput B vs) β θ) ≫ c₀ = _
  rw [show jointInnerCell R L V P (indexInput A us) (indexInput B vs) β θ =
      (fun x y => eqToHom (e (x,y)) ≫ g (x,y)) from
        funext fun x => funext fun y => jointIndexedInner_agrees R L us vs V P A B β θ (x,y),
    ← actRect_seq, rr]
  simp only [Category.assoc]
  rw [reassoc_of% hp, reassoc_of% h₁, h₂]
  rw [show (fun x => rectWordChart (K ∘ jointInnerTag x) (us x.1) (vs x.2) ≫ g x) = _ from funext h₃]

end ActualJoint

set_option backward.isDefEq.respectTransparency false in
theorem taggedRaggedRows_tag_heq {P U Q Q' : Type u} (A : Q' → C) (f : Q → Q')
    (g : P → U → Q) (L : P → List U) (ps : List P) :
    HEq (taggedRaggedRows (A ∘ f) g L ps)
      (taggedRaggedRows A (fun x => f ∘ g x) L ps) := by
  let M := fun x => (L x).map (g x)
  let E := fun x => ((L x).map (f ∘ g x))
  let G := fold 𝒮 Zₐ A
  let q : (ps.flatMap E) = ps.flatMap (fun x => (M x).map f) :=
    congrArg (fun H => ps.flatMap H) (funext fun x => (List.map_map (l:=L x)).symm)
  let e := (congrArg G q).trans (rows_relabel_obj A f M ps)
  apply heq_of_paste e.symm rfl
  rw [eqToHom_refl, Category.comp_id]
  have ht (x : P) : (M x).map f = E x := List.map_map
  have H := rowsChart_rows_congr A ht ps
  have h := rowsChart_relabel_input A f M ps
  let j := fun x => std_fold_map (A ∘ f) (g x) (L x)
  let k := fun x => std_fold_map A (f ∘ g x) (L x)
  let b := fun x => std_fold_map A f (M x)
  let r := fun x => congrArg G (ht x)
  have m (x : P) : eqToHom (b x) ≫ eqToHom (j x) = eqToHom (r x) ≫ eqToHom (k x) := by
    rw [eqToHom_trans, eqToHom_trans]
  have S : act 𝒮 Zₐ (fun x => eqToHom (b x)) ps ≫ act 𝒮 Zₐ (fun x => eqToHom (j x)) ps =
      act 𝒮 Zₐ (fun x => eqToHom (r x)) ps ≫ act 𝒮 Zₐ (fun x => eqToHom (k x)) ps := by
    exact (act_seq 𝒮 Zₐ (fun x => eqToHom (b x)) (fun x => eqToHom (j x)) ps).trans
      ((congrArg (fun g => act 𝒮 Zₐ g ps) (funext m)).trans
        (act_seq 𝒮 Zₐ (fun x => eqToHom (r x)) (fun x => eqToHom (k x)) ps).symm)
  change rowsChart (A ∘ f) M ps ≫ act 𝒮 Zₐ (fun x => eqToHom (j x)) ps =
    eqToHom e.symm ≫ (rowsChart A E ps ≫ act 𝒮 Zₐ (fun x => eqToHom (k x)) ps)
  have h' := congrArg (fun z => z ≫ act 𝒮 Zₐ (fun x => eqToHom (j x)) ps) h
  simp only [Category.assoc] at h'
  rw [S, reassoc_of% H] at h'
  have z := congrArg (fun j => eqToHom (rows_relabel_obj A f M ps).symm ≫ j) h'
  simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] at z
  exact z.symm

set_option backward.isDefEq.respectTransparency false in
theorem taggedRaggedRows_index_heq {P P' U Q : Type u} (A : Q → C)
    (g : P' → U → Q) (L : P' → List U) (f : P → P') (ps : List P) :
    HEq (taggedRaggedRows A g L (ps.map f))
      (taggedRaggedRows A (g ∘ f) (L ∘ f) ps) := by
  let H := fun x => fold 𝒮 Zₐ (A ∘ g x) (L x)
  let M := fun x => (L x).map (g x)
  let K := fold 𝒮 Zₐ A
  let a := congrArg K (List.flatMap_map f M ps)
  let b := std_fold_map H f ps
  have h := taggedRaggedRows_read_parents A H g L f ps (fun x => 𝟙 (H x))
  have j₁ : act 𝒮 Zₐ (fun x => 𝟙 (H x)) (ps.map f) = 𝟙 _ := act_id_grid _
  have j₂ : act 𝒮 Zₐ (fun x => 𝟙 (H (f x))) ps = 𝟙 _ := act_id_grid _
  change taggedRaggedRows A g L (ps.map f) ≫ act 𝒮 Zₐ (fun x => 𝟙 (H x)) (ps.map f) ≫ eqToHom b =
    eqToHom a ≫ taggedRaggedRows A (g ∘ f) (L ∘ f) ps ≫ act 𝒮 Zₐ (fun x => 𝟙 (H (f x))) ps at h
  rw [j₁, j₂, Category.id_comp] at h
  let p := taggedRaggedRows A (g ∘ f) (L ∘ f) ps
  change _ = eqToHom a ≫ p ≫ 𝟙 _ at h
  rw [Category.comp_id p] at h
  exact heq_of_paste a b h

set_option backward.isDefEq.respectTransparency false in
theorem taggedRaggedRows_lists_heq {P U Q : Type u} (A : Q → C)
    (g : P → U → Q) {L L' : P → List U} (h : ∀ p, L p = L' p) (ps : List P) :
    HEq (taggedRaggedRows A g L ps) (taggedRaggedRows A g L' ps) := by
  have e := funext h
  subst L'
  rfl

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
