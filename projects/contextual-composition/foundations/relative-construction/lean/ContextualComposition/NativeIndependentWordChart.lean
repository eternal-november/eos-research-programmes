module
public import ContextualComposition.NativeIndependentWord
@[expose] public section

namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v w z
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "MC" => symmetricCross (C:=C)
variable {T : Bi (coeff (C:=C))}

set_option backward.isDefEq.respectTransparency false in
/-- The native independent partition diagram after flattening the four
addressed axes, with the literal stable block swap and chart compressions. -/
theorem flat_independent_occurrence_outer (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    (N : GridBinary MC R L) {X U Y W : Type u}
    (A : X → U → C) (B : Y → W → C)
    (xs : List X) (ys : List Y) (us : X → List U) (vs : Y → List W) :
    let D := quadLabels (T:=T) A B
    let t := fourExchangeChart xs ys us vs
    AddressOrder.mapSum additiveStructure D (gridOrder t) ≫
      compressGrid D (fourJointExpr xs ys us vs) ≫
      eqToHom (joint_expr_obj (S:=𝒮) (Z:=Zₐ) (T:=T) A B xs ys us vs) ≫
      outerFirst R L A B xs ys us vs =
    compressGrid D (fourOccurrenceExpr xs ys us vs) ≫
      eqToHom (occurrence_expr_obj (S:=𝒮) (Z:=Zₐ) (T:=T) A B xs ys us vs) ≫
      occurrenceFirst R L A B xs ys us vs := by
  intro D t
  let p := occurrence_expr_obj (S:=𝒮) (Z:=Zₐ) (T:=T) A B xs ys us vs
  let q := joint_expr_obj (S:=𝒮) (Z:=Zₐ) (T:=T) A B xs ys us vs
  let a := GridCircuit.eval MC D t
  let b := exchangeInner (T:=T) MC A B xs ys us vs
  let u := outerFirst R L A B xs ys us vs
  let v := occurrenceFirst R L A B xs ys us vs
  have h : a ≫ eqToHom q = eqToHom p ≫ b :=
    heq_paste p q (fourExchangeChart_eval MC A B xs ys us vs)
  have e : b ≫ u = v := occurrence_outer MC R L N A B xs ys us vs
  have c := compressGrid_order D t
  change AddressOrder.mapSum additiveStructure D (gridOrder t) ≫
    compressGrid D (fourJointExpr xs ys us vs) ≫ eqToHom q ≫ u =
    compressGrid D (fourOccurrenceExpr xs ys us vs) ≫ eqToHom p ≫ v
  rw [← Category.assoc (AddressOrder.mapSum additiveStructure D (gridOrder t)), c]
  simp only [Category.assoc]
  rw [reassoc_of% h, e]

set_option backward.isDefEq.respectTransparency false in
theorem compressGrid_over {I : Type w} {X : Type z} (A : I → C) (P : X → GridExpr I) (xs : List X) :
    compressGrid A (GridExpr.over P xs) ≫ eqToHom (GridExpr.eval_over (S:=𝒮) (Z:=Zₐ) A P xs) =
      eqToHom (congrArg (fold 𝒮 Zₐ A) (GridExpr.leaves_over P xs)) ≫
        rowsChart A (fun x => (P x).leaves) xs ≫ act 𝒮 Zₐ (fun x => compressGrid A (P x)) xs := by
  induction xs with
  | nil =>
    simp only [GridExpr.over, GridExpr.leaves, compressGrid, rowsChart, act, eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  | cons x xs ih =>
    let F := fold 𝒮 Zₐ A
    let B := fun x => GridExpr.eval (S:=𝒮) (Z:=Zₐ) A (P x)
    let s := (P x).leaves
    let t := (GridExpr.over P xs).leaves
    let w := xs.flatMap (fun x => (P x).leaves)
    let e : t = w := GridExpr.leaves_over P xs
    let p := compressGrid A (P x)
    let q := compressGrid A (GridExpr.over P xs)
    let c := rowsChart A (fun x => (P x).leaves) xs
    let d := act 𝒮 Zₐ (fun x => compressGrid A (P x)) xs
    let h : GridExpr.eval (S:=𝒮) (Z:=Zₐ) A (GridExpr.over P xs) = fold 𝒮 Zₐ B xs :=
      GridExpr.eval_over A P xs
    let E : F (s ++ t) = F (s ++ w) := congrArg F (congrArg (fun k => s ++ k) e)
    have a : eqToHom E ≫ join additiveStructure A s w =
        join additiveStructure A s t ≫ (F s ◁ eqToHom (congrArg F e)) :=
      join_tail_congr A s e
    have b : q ≫ eqToHom h = eqToHom (congrArg F e) ≫ c ≫ d := ih
    let EH := congrArg (fun q => B x ⊗ q) h
    change (join additiveStructure A s t ≫ (p ⊗ₘ q)) ≫ eqToHom EH =
      eqToHom E ≫ (join additiveStructure A s w ≫ (𝟙 (F s) ⊗ₘ c)) ≫ (p ⊗ₘ d)
    have wh (a b c : C) (h : b = c) : eqToHom (congrArg (fun q => a ⊗ q) h) = a ◁ eqToHom h := by
      cases h
      simp only [eqToHom_refl, whiskerLeft_id]
    have e₀ : eqToHom EH = B x ◁ eqToHom h := wh _ _ _ h
    rw [e₀, ← id_tensorHom]
    simp only [Category.assoc, tensorHom_comp_tensorHom]
    rw [b, ← Category.assoc (eqToHom E), a, Category.assoc, ← id_tensorHom,
      tensorHom_comp_tensorHom, Category.id_comp]
    have i₁ : p ≫ 𝟙 (B x) = p := Category.comp_id p
    have i₂ : 𝟙 (F s) ≫ p = p := Category.id_comp p
    exact congrArg (fun v => join additiveStructure A s t ≫
      (v ⊗ₘ (eqToHom (congrArg F e) ≫ c ≫ d))) (i₁.trans i₂.symm)

theorem leafWord_pin {I X : Type w} (f : X → I) (xs : List X) :
    (GridExpr.over (fun x => GridExpr.leaf (f x)) xs).leaves = xs.map f := by
  rw [GridExpr.leaves_over]
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simpa only [List.flatMap_cons, GridExpr.leaves, List.singleton_append, List.map_cons] using congrArg (List.cons (f x)) ih

set_option backward.isDefEq.respectTransparency false in
theorem compressGrid_leafWord {I X : Type w} (A : I → C) (f : X → I) (xs : List X) :
    compressGrid A (GridExpr.over (fun x => GridExpr.leaf (f x)) xs) ≫
      eqToHom (GridExpr.eval_over (S:=𝒮) (Z:=Zₐ) A (fun x => GridExpr.leaf (f x)) xs) =
    eqToHom ((congrArg (fold 𝒮 Zₐ A) (leafWord_pin f xs)).trans (std_fold_map A f xs)) := by
  let P := fun x => GridExpr.leaf (f x)
  let Z := fun i : I => [i]
  let C₀ := fold 𝒮 Zₐ A
  let C₁ := fold 𝒮 Zₐ (A ∘ f)
  let J := rowsChart A (fun x => [f x]) xs
  let J' := rowsChart A Z (xs.map f)
  let ρ := fun i : I => (ρ_ (A i)).hom
  let e := congrArg C₀ (GridExpr.leaves_over P xs)
  let d := congrArg C₀ (List.flatMap_map f Z xs).symm
  let u := congrArg C₀ (rowsChart_singletons_index (xs.map f))
  let v := std_fold_map A f xs
  have j : J ≫ act 𝒮 Zₐ (fun x => ρ (f x)) xs ≫ eqToHom v.symm =
      eqToHom d ≫ J' ≫ act 𝒮 Zₐ ρ (xs.map f) :=
    rowsChart_index_apply A Z f ρ xs rfl
  have j' : J' ≫ act 𝒮 Zₐ ρ (xs.map f) = eqToHom u := by
    let k := eqToHom u.symm
    let _ : IsIso k := inferInstanceAs (IsIso (eqToHom u.symm))
    apply (cancel_epi k).mp
    have h := rowsChart_singletons A Z (fun _ => rfl) (xs.map f)
    change k ≫ J' ≫ act 𝒮 Zₐ (fun i => eqToHom rfl ≫ ρ i) (xs.map f) = 𝟙 _ at h
    rw [← Category.assoc] at h
    have hρ : (fun i => eqToHom rfl ≫ ρ i) = ρ := by
      funext i
      simp only [eqToHom_refl, Category.id_comp]
    rw [hρ] at h
    have hk : k ≫ eqToHom u = 𝟙 _ := by
      change eqToHom u.symm ≫ eqToHom u = _
      rw [eqToHom_trans]
      rfl
    rw [hk]
    simpa only [Category.assoc] using h
  have c := compressGrid_over A P xs
  rw [c]
  change eqToHom e ≫ J ≫ act 𝒮 Zₐ (fun x => ρ (f x)) xs = _
  let k := eqToHom v.symm
  let _ : IsIso k := inferInstanceAs (IsIso (eqToHom v.symm))
  apply (cancel_mono k).mp
  change (eqToHom e ≫ J ≫ act 𝒮 Zₐ (fun x => ρ (f x)) xs) ≫ eqToHom v.symm = _
  simp only [Category.assoc]
  rw [j, j', ← Category.assoc (eqToHom e), eqToHom_trans, eqToHom_trans, eqToHom_trans]

set_option backward.isDefEq.respectTransparency false in
theorem rowsChart_rows_congr {I : Type w} {X : Type z} (A : I → C) {L M : X → List I}
    (h : ∀ x, L x = M x) (xs : List X) :
    rowsChart A L xs ≫ act 𝒮 Zₐ (fun x => eqToHom (congrArg (fold 𝒮 Zₐ A) (h x))) xs =
      eqToHom (congrArg (fold 𝒮 Zₐ A) (congrArg (fun k => xs.flatMap k) (funext h))) ≫ rowsChart A M xs := by
  have e : L = M := funext h
  subst M
  have r : (fun x => eqToHom (congrArg (fold 𝒮 Zₐ A) (h x))) =
      fun x => 𝟙 (fold 𝒮 Zₐ A (L x)) := by
    funext x
    change eqToHom (rfl : fold 𝒮 Zₐ A (L x) = fold 𝒮 Zₐ A (L x)) = _
    rw [eqToHom_refl]
  rw [r]
  change rowsChart A L xs ≫ act 𝒮 Zₐ (fun x => 𝟙 (fold 𝒮 Zₐ A (L x))) xs = 𝟙 _ ≫ rowsChart A L xs
  have t : act 𝒮 Zₐ (fun x => 𝟙 (fold 𝒮 Zₐ A (L x))) xs = 𝟙 _ := act_id_grid xs
  rw [t, Category.comp_id, Category.id_comp]

def rectPairExpr {X Y : Type w} (xs : List X) (ys : List Y) : GridExpr (X × Y) :=
  GridExpr.over (fun x => GridExpr.over (fun y => .leaf (x,y)) ys) xs

theorem rectPairExpr_leaves {X Y : Type w} (xs : List X) (ys : List Y) :
    (rectPairExpr xs ys).leaves = xs.product ys := by
  unfold rectPairExpr
  rw [GridExpr.leaves_over]
  change _ = xs.flatMap (fun x => ys.map (fun y => (x,y)))
  exact congrArg (fun f => xs.flatMap f) (funext (fun x => leafWord_pin (fun y => (x,y)) ys))

theorem rectPairExpr_eval {X Y : Type w} (A : X × Y → C) (xs : List X) (ys : List Y) :
    GridExpr.eval (S:=𝒮) (Z:=Zₐ) A (rectPairExpr xs ys) =
      fold 𝒮 Zₐ (fun x => fold 𝒮 Zₐ (fun y => A (x,y)) ys) xs := by
  unfold rectPairExpr
  rw [GridExpr.eval_over]
  congr 1
  funext x
  exact GridExpr.eval_over _ _ _

set_option backward.isDefEq.respectTransparency false in
theorem rectPairExpr_chart {X Y : Type w} (A : X × Y → C) (xs : List X) (ys : List Y) :
    compressGrid A (rectPairExpr xs ys) ≫ eqToHom (rectPairExpr_eval A xs ys) =
      eqToHom (congrArg (fold 𝒮 Zₐ A) (rectPairExpr_leaves xs ys)) ≫ rectWordChart (X:=X) (Y:=Y) A xs ys := by
  let P : X → GridExpr (X × Y) := fun x : X => GridExpr.over (fun y => .leaf (x,y)) ys
  let F := fold 𝒮 Zₐ A
  let l := fun x : X => (P x).leaves
  let m := fun x : X => ys.map (fun y => (x,y))
  let p := fun x : X => compressGrid A (P x)
  let r₁ := fun x : X => eqToHom (GridExpr.eval_over (S:=𝒮) (Z:=Zₐ) A (fun y => GridExpr.leaf (x,y)) ys)
  let r₂ := fun x : X => eqToHom (congrArg F (leafWord_pin (fun y => (x,y)) ys))
  let r₃ := fun x : X => eqToHom (std_fold_map A (fun y => (x,y)) ys)
  let a := eqToHom (congrArg F (GridExpr.leaves_over P xs))
  let b := eqToHom (congrArg F (congrArg (fun k => xs.flatMap k) (funext (fun x : X => leafWord_pin (fun y => (x,y)) ys))))
  have h (x : X) : p x ≫ r₁ x = r₂ x ≫ r₃ x := by
    have e := compressGrid_leafWord A (fun y => (x,y)) ys
    exact e.trans (eqToHom_trans _ _).symm
  have h₁ : eqToHom (rectPairExpr_eval A xs ys) =
      eqToHom (GridExpr.eval_over (S:=𝒮) (Z:=Zₐ) A P xs) ≫ act 𝒮 Zₐ r₁ xs := by
    rw [std_act_eqToHom, eqToHom_trans]
  rw [h₁, ← Category.assoc]
  change (compressGrid A (GridExpr.over P xs) ≫
    eqToHom (GridExpr.eval_over (S:=𝒮) (Z:=Zₐ) A P xs)) ≫ act 𝒮 Zₐ r₁ xs = _
  rw [compressGrid_over]
  simp only [Category.assoc]
  change a ≫ rowsChart A l xs ≫ act 𝒮 Zₐ p xs ≫ act 𝒮 Zₐ r₁ xs = _
  have hh : act 𝒮 Zₐ p xs ≫ act 𝒮 Zₐ r₁ xs = act 𝒮 Zₐ r₂ xs ≫ act 𝒮 Zₐ r₃ xs :=
    (act_seq 𝒮 Zₐ p r₁ xs).trans ((congrArg (fun q => act 𝒮 Zₐ q xs) (funext h)).trans (act_seq 𝒮 Zₐ r₂ r₃ xs).symm)
  have k : rowsChart A l xs ≫ act 𝒮 Zₐ r₂ xs = b ≫ rowsChart A m xs :=
    rowsChart_rows_congr A (fun x : X => leafWord_pin (fun y => (x,y)) ys) xs
  rw [hh, ← Category.assoc (rowsChart A l xs), k]
  let m₁ := congrArg F (GridExpr.leaves_over P xs)
  let m₂ := congrArg F (congrArg (fun k => xs.flatMap k) (funext (fun x : X => leafWord_pin (fun y => (x,y)) ys)))
  change eqToHom m₁ ≫ (eqToHom m₂ ≫ rowsChart A m xs) ≫ act 𝒮 Zₐ r₃ xs =
    eqToHom (m₁.trans m₂) ≫ (rowsChart A m xs ≫ act 𝒮 Zₐ r₃ xs)
  simp only [Category.assoc]
  rw [reassoc_of% eqToHom_trans m₁ m₂]

set_option backward.isDefEq.respectTransparency false in
theorem compressGrid_pair_context {I X Y : Type w} (A : I → C) (P : X × Y → GridExpr I)
    (xs : List X) (ys : List Y) :
    let M := fun x => GridExpr.over (fun y => P (x,y)) ys
    let L := fun p => (P p).leaves
    let B := fun p => GridExpr.eval (S:=𝒮) (Z:=Zₐ) A (P p)
    let e : (GridExpr.over M xs).leaves = (xs.product ys).flatMap L :=
      (GridExpr.leaves_over M xs).trans ((congrArg (fun k => xs.flatMap k)
        (funext fun x => GridExpr.leaves_over (fun y => P (x,y)) ys)).trans
          ((List.flatMap_assoc (l:=xs) (f:=fun x => ys.map (fun y => (x,y))) (g:=L)).trans
            (congrArg (fun k => xs.flatMap k) (funext fun x => List.flatMap_map (fun y => (x,y)) L ys))).symm)
    let E : GridExpr.eval (S:=𝒮) (Z:=Zₐ) A (GridExpr.over M xs) =
        fold 𝒮 Zₐ (fun x => fold 𝒮 Zₐ (fun y => B (x,y)) ys) xs :=
      (GridExpr.eval_over A M xs).trans (congrArg (fun k => fold 𝒮 Zₐ k xs)
        (funext fun x => GridExpr.eval_over A (fun y => P (x,y)) ys))
    compressGrid A (GridExpr.over M xs) ≫ eqToHom E =
      eqToHom (congrArg (fold 𝒮 Zₐ A) e) ≫ rowsChart A L (xs.product ys) ≫
        act 𝒮 Zₐ (fun p => compressGrid A (P p)) (xs.product ys) ≫ rectWordChart B xs ys := by
  intro M L B e E
  let F := fold 𝒮 Zₐ A
  let L₁ := fun x => (M x).leaves
  let L₂ := fun x => ys.flatMap (fun y => L (x,y))
  let l := fun x => GridExpr.leaves_over (fun y => P (x,y)) ys
  let a := eqToHom (congrArg F (GridExpr.leaves_over M xs))
  let b := eqToHom (congrArg F (congrArg (fun k => xs.flatMap k) (funext l)))
  let s := fun p => compressGrid A (P p)
  let h := fun x => compressGrid A (M x)
  let j := fun x => eqToHom (GridExpr.eval_over (S:=𝒮) (Z:=Zₐ) A (fun y => P (x,y)) ys)
  let r := fun x => rowsChart A (fun y => L (x,y)) ys
  let t := fun x => act 𝒮 Zₐ (fun y => s (x,y)) ys
  let c := fun x => eqToHom (congrArg F (l x))
  have H (x : X) : h x ≫ j x = c x ≫ r x ≫ t x :=
    compressGrid_over A (fun y => P (x,y)) ys
  have H₁ : act 𝒮 Zₐ h xs ≫ act 𝒮 Zₐ j xs =
      act 𝒮 Zₐ c xs ≫ act 𝒮 Zₐ r xs ≫ act 𝒮 Zₐ t xs := by
    have h₀ := act_seq 𝒮 Zₐ h j xs
    have h₁ := act_seq 𝒮 Zₐ c (fun x => r x ≫ t x) xs
    have h₂ := act_seq 𝒮 Zₐ r t xs
    exact h₀.trans ((congrArg (fun g => act 𝒮 Zₐ g xs) (funext H)).trans
      (h₁.symm.trans (congrArg (fun g => act 𝒮 Zₐ c xs ≫ g) h₂.symm)))
  have H₂ : rowsChart A L₁ xs ≫ act 𝒮 Zₐ c xs = b ≫ rowsChart A L₂ xs :=
    rowsChart_rows_congr A l xs
  have H₃ : eqToHom E = eqToHom (GridExpr.eval_over (S:=𝒮) (Z:=Zₐ) A M xs) ≫ act 𝒮 Zₐ j xs := by
    rw [std_act_eqToHom, eqToHom_trans]
  let U := fun p => F (L p)
  have h₃ : act 𝒮 Zₐ s (xs.product ys) ≫ rectWordChart B xs ys =
      rectWordChart U xs ys ≫ act 𝒮 Zₐ t xs := rectWordChart_natural s xs ys
  have h₄ := rowsChart_rectWord A L xs ys
  dsimp only at h₄
  rw [H₃, ← Category.assoc, compressGrid_over]
  simp only [Category.assoc]
  change a ≫ rowsChart A L₁ xs ≫ (act 𝒮 Zₐ h xs ≫ act 𝒮 Zₐ j xs) =
    eqToHom (congrArg F e) ≫ rowsChart A L (xs.product ys) ≫ (act 𝒮 Zₐ s (xs.product ys) ≫ rectWordChart B xs ys)
  rw [H₁, h₃, reassoc_of% H₂, reassoc_of% h₄]
  let d := (List.flatMap_assoc (l:=xs) (f:=fun x => ys.map (fun y => (x,y))) (g:=L)).trans
    (congrArg (fun k => xs.flatMap k) (funext fun x => List.flatMap_map (fun y => (x,y)) L ys))
  let p := congrArg F e
  let q := congrArg F d
  let a₀ := congrArg F (GridExpr.leaves_over M xs)
  let b₀ := congrArg F (congrArg (fun k => xs.flatMap k) (funext l))
  change eqToHom a₀ ≫ eqToHom b₀ ≫ rowsChart A L₂ xs ≫ act 𝒮 Zₐ r xs ≫ act 𝒮 Zₐ t xs =
    eqToHom p ≫ eqToHom q ≫ rowsChart A L₂ xs ≫ act 𝒮 Zₐ r xs ≫ act 𝒮 Zₐ t xs
  rw [reassoc_of% eqToHom_trans a₀ b₀, reassoc_of% eqToHom_trans p q]

set_option backward.isDefEq.respectTransparency false in
theorem compressGrid_partition_context {X Y I : Type w} (A : I → C) (P : X → GridExpr I)
    (rows : Y → List X) (ys : List Y) :
    let L := fun x => (P x).leaves
    let B := fun x => GridExpr.eval (S:=𝒮) (Z:=Zₐ) A (P x)
    let M := fun y => GridExpr.over P (rows y)
    let t := ys.flatMap rows
    let e : (GridExpr.over M ys).leaves = t.flatMap L :=
      (GridExpr.leaves_over M ys).trans ((congrArg (fun k => ys.flatMap k)
        (funext fun y => GridExpr.leaves_over P (rows y))).trans List.flatMap_assoc.symm)
    let E : GridExpr.eval (S:=𝒮) (Z:=Zₐ) A (GridExpr.over M ys) =
      fold 𝒮 Zₐ (fun y => fold 𝒮 Zₐ B (rows y)) ys :=
      (GridExpr.eval_over A M ys).trans (congrArg (fun k => fold 𝒮 Zₐ k ys)
        (funext fun y => GridExpr.eval_over A P (rows y)))
    compressGrid A (GridExpr.over M ys) ≫ eqToHom E =
      eqToHom (congrArg (fold 𝒮 Zₐ A) e) ≫ rowsChart A L t ≫
        act 𝒮 Zₐ (fun x => compressGrid A (P x)) t ≫ rowsChart B rows ys := by
  intro L B M t e E
  let F := fold 𝒮 Zₐ A
  let L₁ := fun y => (M y).leaves
  let L₂ := fun y => (rows y).flatMap L
  let l := fun y => GridExpr.leaves_over P (rows y)
  let a := eqToHom (congrArg F (GridExpr.leaves_over M ys))
  let b := eqToHom (congrArg F (congrArg (fun k => ys.flatMap k) (funext l)))
  let s := fun x => compressGrid A (P x)
  let h := fun y => compressGrid A (M y)
  let j := fun y => eqToHom (GridExpr.eval_over (S:=𝒮) (Z:=Zₐ) A P (rows y))
  let r := fun y => rowsChart A L (rows y)
  let k := fun y => act 𝒮 Zₐ s (rows y)
  let c := fun y => eqToHom (congrArg F (l y))
  have H (y : Y) : h y ≫ j y = c y ≫ r y ≫ k y := compressGrid_over A P (rows y)
  have H₁ : act 𝒮 Zₐ h ys ≫ act 𝒮 Zₐ j ys =
      act 𝒮 Zₐ c ys ≫ act 𝒮 Zₐ r ys ≫ act 𝒮 Zₐ k ys := by
    have h₀ := act_seq 𝒮 Zₐ h j ys
    have h₁ := act_seq 𝒮 Zₐ c (fun x => r x ≫ k x) ys
    have h₂ := act_seq 𝒮 Zₐ r k ys
    exact h₀.trans ((congrArg (fun g => act 𝒮 Zₐ g ys) (funext H)).trans
      (h₁.symm.trans (congrArg (fun g => act 𝒮 Zₐ c ys ≫ g) h₂.symm)))
  have H₂ : rowsChart A L₁ ys ≫ act 𝒮 Zₐ c ys = b ≫ rowsChart A L₂ ys :=
    rowsChart_rows_congr A l ys
  have H₃ : eqToHom E = eqToHom (GridExpr.eval_over (S:=𝒮) (Z:=Zₐ) A M ys) ≫ act 𝒮 Zₐ j ys := by
    rw [std_act_eqToHom, eqToHom_trans]
  let U := fun x => F (L x)
  have hn : act 𝒮 Zₐ s t ≫ rowsChart B rows ys = rowsChart U rows ys ≫ act 𝒮 Zₐ k ys :=
    rowsChart_natural rows s ys
  have hi := rowsChart_iterated A L rows ys
  rw [H₃, ← Category.assoc, compressGrid_over]
  simp only [Category.assoc]
  change a ≫ rowsChart A L₁ ys ≫ (act 𝒮 Zₐ h ys ≫ act 𝒮 Zₐ j ys) =
    eqToHom (congrArg F e) ≫ rowsChart A L t ≫ (act 𝒮 Zₐ s t ≫ rowsChart B rows ys)
  rw [H₁, hn, reassoc_of% H₂]
  let d : ys.flatMap L₂ = t.flatMap L := List.flatMap_assoc.symm
  let p := congrArg F e
  let q := congrArg F d
  let a₀ := congrArg F (GridExpr.leaves_over M ys)
  let b₀ := congrArg F (congrArg (fun k => ys.flatMap k) (funext l))
  let u := rowsChart A L t
  let v := rowsChart U rows ys
  have h' : eqToHom q ≫ u ≫ v = rowsChart A L₂ ys ≫ act 𝒮 Zₐ r ys := hi
  have h'' := congrArg (fun z => eqToHom a₀ ≫ eqToHom b₀ ≫ z ≫ act 𝒮 Zₐ k ys) h'.symm
  simp only [Category.assoc] at h''
  refine h''.trans ?_
  change eqToHom a₀ ≫ eqToHom b₀ ≫ eqToHom q ≫ u ≫ v ≫ act 𝒮 Zₐ k ys =
    eqToHom p ≫ u ≫ v ≫ act 𝒮 Zₐ k ys
  rw [reassoc_of% eqToHom_trans a₀ b₀, reassoc_of% eqToHom_trans (a₀.trans b₀) q]

set_option backward.isDefEq.respectTransparency false in
theorem compressGrid_pair_context_post {I X Y : Type w} (A : I → C) (P : X × Y → GridExpr I)
    (xs : List X) (ys : List Y) (D : X × Y → C)
    (g : ∀ p, GridExpr.eval (S:=𝒮) (Z:=Zₐ) A (P p) ⟶ D p) :
    let M := fun x => GridExpr.over (fun y => P (x,y)) ys
    let L := fun p => (P p).leaves
    let B := fun p => GridExpr.eval (S:=𝒮) (Z:=Zₐ) A (P p)
    let e : (GridExpr.over M xs).leaves = (xs.product ys).flatMap L :=
      (GridExpr.leaves_over M xs).trans ((congrArg (fun k => xs.flatMap k)
        (funext fun x => GridExpr.leaves_over (fun y => P (x,y)) ys)).trans
          ((List.flatMap_assoc (l:=xs) (f:=fun x => ys.map (fun y => (x,y))) (g:=L)).trans
            (congrArg (fun k => xs.flatMap k) (funext fun x => List.flatMap_map (fun y => (x,y)) L ys))).symm)
    let E : GridExpr.eval (S:=𝒮) (Z:=Zₐ) A (GridExpr.over M xs) =
        fold 𝒮 Zₐ (fun x => fold 𝒮 Zₐ (fun y => B (x,y)) ys) xs :=
      (GridExpr.eval_over A M xs).trans (congrArg (fun k => fold 𝒮 Zₐ k xs)
        (funext fun x => GridExpr.eval_over A (fun y => P (x,y)) ys))
    compressGrid A (GridExpr.over M xs) ≫ eqToHom E ≫
      act 𝒮 Zₐ (fun x => act 𝒮 Zₐ (fun y => g (x,y)) ys) xs =
      eqToHom (congrArg (fold 𝒮 Zₐ A) e) ≫ rowsChart A L (xs.product ys) ≫
        act 𝒮 Zₐ (fun p => compressGrid A (P p) ≫ g p) (xs.product ys) ≫ rectWordChart D xs ys := by
  intro M L B e E
  rw [← Category.assoc, compressGrid_pair_context]
  simp only [Category.assoc]
  rw [← rectWordChart_natural g xs ys]
  rw [← Category.assoc (act 𝒮 Zₐ (fun p => compressGrid A (P p)) (xs.product ys))]
  have h := act_seq 𝒮 Zₐ (fun p => compressGrid A (P p)) g (xs.product ys)
  exact congrArg (fun k => eqToHom (congrArg (fold 𝒮 Zₐ A) e) ≫ rowsChart A L (xs.product ys) ≫
    k ≫ rectWordChart D xs ys) h

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
