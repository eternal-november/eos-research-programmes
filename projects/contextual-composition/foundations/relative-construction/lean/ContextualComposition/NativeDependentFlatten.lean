module
public import ContextualComposition.NativeSelectedParentBlock
@[expose] public section
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v w
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C

theorem dependentExpr_raggedEval {X Y : Type w} (A : X × Y → C) (xs : List X) (ys : X → List Y) :
    GridExpr.eval (S:=𝒮) (Z:=Zₐ) A (dependentExpr xs ys) =
      fold 𝒮 Zₐ (fun x => fold 𝒮 Zₐ (fun y => A (x,y)) (ys x)) xs := by
  unfold dependentExpr
  rw [GridExpr.eval_over]
  congr 1
  funext x
  exact GridExpr.eval_over _ _ _

set_option backward.isDefEq.respectTransparency false in
theorem dependentExpr_raggedRows {X Y : Type w} (A : X × Y → C) (xs : List X) (ys : X → List Y) :
    compressGrid A (dependentExpr xs ys) ≫ eqToHom (dependentExpr_raggedEval A xs ys) =
      eqToHom (congrArg (fold 𝒮 Zₐ A) (dependentExpr_leaves xs ys)) ≫ taggedRaggedRows A (fun x y => (x,y)) ys xs := by
  let P : X → GridExpr (X × Y) := fun x : X => GridExpr.over (fun y => .leaf (x,y)) (ys x)
  let F := fold 𝒮 Zₐ A
  let l := fun x : X => (P x).leaves
  let m := fun x : X => (ys x).map (fun y => (x,y))
  let p := fun x : X => compressGrid A (P x)
  let r₁ := fun x : X => eqToHom (GridExpr.eval_over (S:=𝒮) (Z:=Zₐ) A (fun y => GridExpr.leaf (x,y)) (ys x))
  let r₂ := fun x : X => eqToHom (congrArg F (leafWord_pin (fun y => (x,y)) (ys x)))
  let r₃ := fun x : X => eqToHom (std_fold_map A (fun y => (x,y)) (ys x))
  let a := eqToHom (congrArg F (GridExpr.leaves_over P xs))
  let b := eqToHom (congrArg F (congrArg (fun k => xs.flatMap k) (funext (fun x : X => leafWord_pin (fun y => (x,y)) (ys x)))))
  have h (x : X) : p x ≫ r₁ x = r₂ x ≫ r₃ x := by
    have e := compressGrid_leafWord A (fun y => (x,y)) (ys x)
    exact e.trans (eqToHom_trans _ _).symm
  have h₁ : eqToHom (dependentExpr_raggedEval A xs ys) =
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
    rowsChart_rows_congr A (fun x : X => leafWord_pin (fun y => (x,y)) (ys x)) xs
  rw [hh, ← Category.assoc (rowsChart A l xs), k]
  let m₁ := congrArg F (GridExpr.leaves_over P xs)
  let m₂ := congrArg F (congrArg (fun k => xs.flatMap k) (funext (fun x : X => leafWord_pin (fun y => (x,y)) (ys x))))
  change eqToHom m₁ ≫ (eqToHom m₂ ≫ rowsChart A m xs) ≫ act 𝒮 Zₐ r₃ xs =
    eqToHom (m₁.trans m₂) ≫ (rowsChart A m xs ≫ act 𝒮 Zₐ r₃ xs)
  simp only [Category.assoc]
  rw [reassoc_of% eqToHom_trans m₁ m₂]

set_option backward.isDefEq.respectTransparency false in
theorem dependentWordAug_raw_rows {X Y : Type u} {T : Bi (coeff (C:=C))}
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ) {I : C} (J : UnitCompat R I)
    (xs : List X) (ys : X → List Y) (V : X → C) (W : X → Y → C)
    (δ : ∀ x, fold 𝒮 Zₐ (W x) (ys x) ⟶ I) (ε : fold 𝒮 Zₐ V xs ⟶ I) :
    dependentWordAugCell R L J xs ys V W (fun x => eqToHom (std_fold_map id (W x) (ys x)) ≫ δ x) ε =
      taggedRaggedRows (dependentLabels (T:=T) V W) (fun x y => (x,y)) ys xs ≫
      act 𝒮 Zₐ (fun x => (Lin.left L (V x)).collect (W x) (ys x) ≫
         T.map (𝟙 (V x)) (δ x) ≫ J.ρ (V x)) xs ≫ ε := by
  let A := dependentLabels (T:=T) V W
  let G := fold 𝒮 Zₐ A
  let B := indexInput W ys
  let δ₀ := fun x => eqToHom (std_fold_map id (W x) (ys x)) ≫ δ x
  let P := fun x => sourceRow L J V B δ₀ x
  let Q := fun x => (Lin.left L (V x)).collect (W x) (ys x) ≫ T.map (𝟙 (V x)) (δ x) ≫ J.ρ (V x)
  let b := fun x => eqToHom (std_fold_map (T.obj (V x)) (W x) (ys x))
  have h (x : X) : P x = b x ≫ Q x := by
    let F := Lin.left L (V x)
    let H := leftFactor T (V x)
    let d := std_fold_map id (W x) (ys x)
    let a := std_fold_map (T.obj (V x)) (W x) (ys x)
    have k : F.collect id ((ys x).map (W x)) ≫ eqToHom (congrArg F.obj d) =
      eqToHom a ≫ F.collect (W x) (ys x) := heq_paste a (congrArg F.obj d) (lin_collect_relabel F id (W x) (ys x))
    have m : H.map (eqToHom d) = eqToHom (congrArg F.obj d) := by
      have g (u v : C) (e : u = v) : H.map (eqToHom e) = eqToHom (congrArg F.obj e) := by
        cases e
        rw [eqToHom_refl, eqToHom_refl, H.map_id]
      exact g _ _ d
    unfold P sourceRow rowAt
    change (gatherLeft L (V x) ((ys x).map (W x)) ≫ H.map (eqToHom d ≫ δ x)) ≫ J.ρ (V x) = _
    rw [← collect_left_eq, H.map_comp, m]
    simp only [Category.assoc]
    rw [reassoc_of% k]
  have ha : act 𝒮 Zₐ P xs = act 𝒮 Zₐ b xs ≫ act 𝒮 Zₐ Q xs :=
    (congrArg (fun k => act 𝒮 Zₐ k xs) (funext h)).trans (act_seq 𝒮 Zₐ b Q xs).symm
  have hb : eqToHom (dependentExpr_eval (T:=T) V W xs ys) ≫ act 𝒮 Zₐ b xs =
      eqToHom (dependentExpr_raggedEval A xs ys) := by
    rw [std_act_eqToHom, eqToHom_trans]
  have hc : augmentation L J V B xs δ₀ ε = act 𝒮 Zₐ P xs ≫ ε := by
    rfl
  let d := congrArg G (dependentExpr_leaves xs ys)
  unfold dependentWordAugCell
  change eqToHom d.symm ≫ compressGrid A (dependentExpr xs ys) ≫
    eqToHom (dependentExpr_eval (T:=T) V W xs ys) ≫ augmentation L J V B xs δ₀ ε = _
  rw [hc, ha]
  simp only [Category.assoc]
  rw [reassoc_of% hb, reassoc_of% dependentExpr_raggedRows A xs ys]
  have inv : eqToHom d.symm ≫ eqToHom d = 𝟙 _ := by
    rw [eqToHom_trans]
    rfl
  rw [reassoc_of% inv]

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
