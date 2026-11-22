module
public import ContextualComposition.NativeDependentChildChart
@[expose] public section

/-! Transport raw occurrence addresses without changing the chart or its
additive compression. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v w z
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
variable {X : Type w} {Y : Type z}

def retagGrid (f : X → Y) : GridExpr X → GridExpr Y
  | .zero => .zero
  | .leaf x => .leaf (f x)
  | .bin b c => .bin (retagGrid f b) (retagGrid f c)

theorem retagGrid_leaves (f : X → Y) (t : GridExpr X) :
    (retagGrid f t).leaves = t.leaves.map f := by
  induction t with
  | zero => rfl
  | leaf x => rfl
  | bin b c ih₁ ih₂ => simp only [retagGrid, GridExpr.leaves, ih₁, ih₂, List.map_append]

theorem retagGrid_eval (A : Y → C) (f : X → Y) (t : GridExpr X) :
    GridExpr.eval (S:=𝒮) (Z:=Zₐ) A (retagGrid f t) =
      GridExpr.eval (S:=𝒮) (Z:=Zₐ) (A ∘ f) t := by
  induction t with
  | zero => rfl
  | leaf x => rfl
  | bin b c ih₁ ih₂ => simp only [retagGrid, GridExpr.eval, ih₁, ih₂]

set_option backward.isDefEq.respectTransparency false in
theorem compressGrid_retag (A : Y → C) (f : X → Y) (t : GridExpr X) :
    compressGrid A (retagGrid f t) ≫ eqToHom (retagGrid_eval A f t) =
      eqToHom ((congrArg (fold 𝒮 Zₐ A) (retagGrid_leaves f t)).trans (std_fold_map A f t.leaves)) ≫
        compressGrid (A ∘ f) t := by
  induction t with
  | zero =>
    change 𝟙 Zₐ ≫ 𝟙 Zₐ = 𝟙 Zₐ ≫ 𝟙 Zₐ
    rfl
  | leaf x =>
    change (ρ_ (A (f x))).hom ≫ 𝟙 _ = 𝟙 _ ≫ (ρ_ (A (f x))).hom
    rw [Category.comp_id, Category.id_comp]
  | bin b c ih₁ ih₂ =>
    let H := fold 𝒮 Zₐ A
    let G := fold 𝒮 Zₐ (A ∘ f)
    let bs := b.leaves
    let cs := c.leaves
    let b₀ := (retagGrid f b).leaves
    let c₀ := (retagGrid f c).leaves
    let r := retagGrid_leaves f b
    let s := retagGrid_leaves f c
    let ep := congrArg H r
    let eq := congrArg H s
    let p := std_fold_map A f bs
    let q := std_fold_map A f cs
    let U := compressGrid A (retagGrid f b)
    let V := compressGrid A (retagGrid f c)
    let U' := compressGrid (A ∘ f) b
    let V' := compressGrid (A ∘ f) c
    let a := retagGrid_eval A f b
    let d := retagGrid_eval A f c
    let F₁ := GridExpr.eval (S:=𝒮) (Z:=Zₐ) A (retagGrid f b)
    let F₂ := GridExpr.eval (S:=𝒮) (Z:=Zₐ) A (retagGrid f c)
    let E := congrArg₂ (fun x y : C => x ⊗ y) a d
    have hCast {x x' y y' : C} (e : x = x') (h : y = y') :
        eqToHom (congrArg₂ (fun x y : C => x ⊗ y) e h) = eqToHom e ⊗ₘ eqToHom h := by
      cases e
      cases h
      simp only [eqToHom_refl, tensorHom_id, id_whiskerRight]
    have jc {xs xs' ys ys' : List Y} (e : xs = xs') (j : ys = ys') :
        join additiveStructure A xs ys ≫ (eqToHom (congrArg H e) ⊗ₘ eqToHom (congrArg H j)) =
          eqToHom (congrArg H (congrArg₂ List.append e j)) ≫ join additiveStructure A xs' ys' := by
      cases e
      cases j
      simp only [eqToHom_refl, tensorHom_id, id_whiskerRight, Category.id_comp]
      exact Category.comp_id _
    let m := congrArg H (congrArg₂ List.append r s)
    let n := fold_map_append A f (xs:=bs) (ys:=cs)
    have hJoin : join additiveStructure A b₀ c₀ ≫
        (eqToHom (ep.trans p) ⊗ₘ eqToHom (eq.trans q)) =
        eqToHom (m.trans n) ≫ join additiveStructure (A ∘ f) bs cs := by
      rw [← eqToHom_trans ep p, ← eqToHom_trans eq q, ← tensorHom_comp_tensorHom]
      rw [← Category.assoc, jc r s, Category.assoc, join_relabel, ← Category.assoc, eqToHom_trans]
      rfl
    change (join additiveStructure A b₀ c₀ ≫ (U ⊗ₘ V)) ≫ eqToHom E =
      eqToHom (m.trans n) ≫ (join additiveStructure (A ∘ f) bs cs ≫ (U' ⊗ₘ V'))
    rw [hCast a d, Category.assoc, tensorHom_comp_tensorHom]
    have ih₁' : U ≫ eqToHom a = eqToHom (ep.trans p) ≫ U' := ih₁
    have ih₂' : V ≫ eqToHom d = eqToHom (eq.trans q) ≫ V' := ih₂
    rw [ih₁', ih₂', ← tensorHom_comp_tensorHom, ← Category.assoc, hJoin, Category.assoc]

section LeafPartition
variable {K U : Type w} {J : Type z}
def leafPartitionExpr (f : U → K) (cols : J → List U) (js : List J) : GridExpr K :=
  GridExpr.over (fun j => GridExpr.over (fun y => .leaf (f y)) (cols j)) js

theorem leafPartition_leaves (f : U → K) (cols : J → List U) (js : List J) :
    (leafPartitionExpr f cols js).leaves = (js.flatMap cols).map (f) := by
  unfold leafPartitionExpr
  rw [GridExpr.leaves_over, List.map_flatMap]
  exact congrArg (fun k => js.flatMap k) (funext fun j => leafWord_pin (f) (cols j))

theorem leafPartition_eval (A : K → C) (f : U → K) (cols : J → List U) (js : List J) :
    GridExpr.eval (S:=𝒮) (Z:=Zₐ) A (leafPartitionExpr f cols js) =
      fold 𝒮 Zₐ (fun j => fold 𝒮 Zₐ (A ∘ f) (cols j)) js := by
  unfold leafPartitionExpr
  rw [GridExpr.eval_over]
  congr 1
  funext j
  exact GridExpr.eval_over _ _ _

set_option backward.isDefEq.respectTransparency false in
theorem leafPartition_chart (A : K → C) (f : U → K) (cols : J → List U) (js : List J) :
    compressGrid A (leafPartitionExpr f cols js) ≫
      eqToHom (leafPartition_eval A f cols js) =
    eqToHom ((congrArg (fold 𝒮 Zₐ A) (leafPartition_leaves f cols js)).trans
      (std_fold_map A (f) (js.flatMap cols))) ≫
      rowsChart (A ∘ f) cols js := by
  let F := fold 𝒮 Zₐ A
  let P := fun j : J => GridExpr.over (fun y => .leaf (f y)) (cols j)
  let L := fun j => (P j).leaves
  let L' := fun j => (cols j).map f
  let a := eqToHom (congrArg F (GridExpr.leaves_over P js))
  let R := rowsChart A L js
  let R' := rowsChart A L' js
  let p := fun j => compressGrid A (P j)
  let c := fun j : J => eqToHom (GridExpr.eval_over (S:=𝒮) (Z:=Zₐ) A (fun y => GridExpr.leaf (f y)) (cols j))
  let d := fun j : J => eqToHom (congrArg F (leafWord_pin f (cols j)))
  let z := fun j : J => eqToHom (std_fold_map A f (cols j))
  have h (j : J) : p j ≫ c j = d j ≫ z j :=
    (compressGrid_leafWord A f (cols j)).trans (eqToHom_trans _ _).symm
  have e : eqToHom (leafPartition_eval A f cols js) =
      eqToHom (GridExpr.eval_over (S:=𝒮) (Z:=Zₐ) A P js) ≫ act 𝒮 Zₐ c js := by
    rw [std_act_eqToHom, eqToHom_trans]
  rw [e, ← Category.assoc]
  change (compressGrid A (GridExpr.over P js) ≫ eqToHom (GridExpr.eval_over (S:=𝒮) (Z:=Zₐ) A P js)) ≫
    act 𝒮 Zₐ c js = _
  rw [compressGrid_over]
  simp only [Category.assoc]
  let e₀ := congrArg F (congrArg (fun k => js.flatMap k) (funext (fun j => leafWord_pin f (cols j))))
  let e₁ := rows_relabel_obj A f cols js
  let b := eqToHom e₀
  let k := eqToHom e₁
  have h₀ : act 𝒮 Zₐ p js ≫ act 𝒮 Zₐ c js = act 𝒮 Zₐ d js ≫ act 𝒮 Zₐ z js :=
    (act_seq 𝒮 Zₐ p c js).trans ((congrArg (fun q => act 𝒮 Zₐ q js) (funext h)).trans (act_seq 𝒮 Zₐ d z js).symm)
  have h₁ : R ≫ act 𝒮 Zₐ d js = b ≫ R' := rowsChart_rows_congr A (fun j => leafWord_pin f (cols j)) js
  have h₂ : R' ≫ act 𝒮 Zₐ z js = k ≫ rowsChart (A ∘ f) cols js :=
    rowsChart_relabel_input A f cols js
  let π := congrArg F (GridExpr.leaves_over P js)
  change a ≫ R ≫ (act 𝒮 Zₐ p js ≫ act 𝒮 Zₐ c js) =
    eqToHom ((π.trans e₀).trans e₁) ≫ rowsChart (A ∘ f) cols js
  rw [h₀, reassoc_of% h₁, h₂]
  change eqToHom π ≫ eqToHom e₀ ≫ eqToHom e₁ ≫ rowsChart (A ∘ f) cols js = _
  rw [reassoc_of% eqToHom_trans π e₀, reassoc_of% eqToHom_trans (π.trans e₀) e₁]


end LeafPartition

section RaggedRows
variable {K U P : Type w} {J : Type z}
def taggedRaggedRows (A : K → C) (f : P → U → K) (L : P → List U) (ps : List P) :
    fold 𝒮 Zₐ A (ps.flatMap (fun p => (L p).map (f p))) ⟶
      fold 𝒮 Zₐ (fun p => fold 𝒮 Zₐ (A ∘ f p) (L p)) ps :=
  rowsChart A (fun p => (L p).map (f p)) ps ≫
    act 𝒮 Zₐ (fun p => eqToHom (std_fold_map A (f p) (L p))) ps

set_option backward.isDefEq.respectTransparency false in
theorem taggedRaggedRows_order (A : K → C) (f : P → U → K) {L M : P → List U}
    (r : ∀ p, AddressOrder U (L p) (M p)) (ps : List P) :
    AddressOrder.mapSum additiveStructure A (rowOrders (fun p => (r p).relabel (f p)) ps) ≫
      taggedRaggedRows A f M ps =
    taggedRaggedRows A f L ps ≫
      act 𝒮 Zₐ (fun p => AddressOrder.mapSum additiveStructure (A ∘ f p) (r p)) ps := by
  let a := fun p => eqToHom (std_fold_map A (f p) (L p))
  let b := fun p => eqToHom (std_fold_map A (f p) (M p))
  let S := rowsChart A (fun p => (L p).map (f p)) ps
  let T := rowsChart A (fun p => (M p).map (f p)) ps
  let r₀ := fun p => AddressOrder.mapSum additiveStructure A ((r p).relabel (f p))
  let r₁ := fun p => AddressOrder.mapSum additiveStructure (A ∘ f p) (r p)
  let z := AddressOrder.mapSum additiveStructure A (rowOrders (fun p => (r p).relabel (f p)) ps)
  have e : z ≫ T = S ≫ act 𝒮 Zₐ r₀ ps := rowsChart_rowOrders A (fun p => (r p).relabel (f p)) ps
  have h (p : P) : r₀ p ≫ b p = a p ≫ r₁ p := (relabel_mapSum A (f p) (r p)).symm
  have h' : act 𝒮 Zₐ r₀ ps ≫ act 𝒮 Zₐ b ps = act 𝒮 Zₐ a ps ≫ act 𝒮 Zₐ r₁ ps :=
    (act_seq 𝒮 Zₐ r₀ b ps).trans ((congrArg (fun u => act 𝒮 Zₐ u ps) (funext h)).trans (act_seq 𝒮 Zₐ a r₁ ps).symm)
  change z ≫ (T ≫ act 𝒮 Zₐ b ps) = (S ≫ act 𝒮 Zₐ a ps) ≫ act 𝒮 Zₐ r₁ ps
  rw [← Category.assoc z, e]
  simp only [Category.assoc, h']

def leafPartitionMatrix (f : P → U → K) (L : P → J → List U) (ps : List P) (js : List J) : GridExpr K :=
  GridExpr.over (fun p => leafPartitionExpr (f p) (L p) js) ps

theorem leafPartitionMatrix_leaves (f : P → U → K) (L : P → J → List U) (ps : List P) (js : List J) :
    (leafPartitionMatrix f L ps js).leaves = ps.flatMap (fun p => (js.flatMap (L p)).map (f p)) :=
  (GridExpr.leaves_over (fun p => leafPartitionExpr (f p) (L p) js) ps).trans
    (congrArg (fun k => ps.flatMap k) (funext (fun p => leafPartition_leaves (f p) (L p) js)))

theorem leafPartitionMatrix_eval (A : K → C) (f : P → U → K) (L : P → J → List U)
    (ps : List P) (js : List J) :
    GridExpr.eval (S:=𝒮) (Z:=Zₐ) A (leafPartitionMatrix f L ps js) =
      fold 𝒮 Zₐ (fun p => fold 𝒮 Zₐ (fun j => fold 𝒮 Zₐ (A ∘ f p) (L p j)) js) ps :=
  (GridExpr.eval_over A (fun p => leafPartitionExpr (f p) (L p) js) ps).trans
    (congrArg (fun k => fold 𝒮 Zₐ k ps) (funext (fun p => leafPartition_eval A (f p) (L p) js)))

set_option backward.isDefEq.respectTransparency false in
theorem leafPartitionMatrix_chart (A : K → C) (f : P → U → K) (L : P → J → List U)
    (ps : List P) (js : List J) :
    compressGrid A (leafPartitionMatrix f L ps js) ≫ eqToHom (leafPartitionMatrix_eval A f L ps js) =
      eqToHom (congrArg (fold 𝒮 Zₐ A) (leafPartitionMatrix_leaves f L ps js)) ≫
        taggedRaggedRows A f (fun p => js.flatMap (L p)) ps ≫
        act 𝒮 Zₐ (fun p => rowsChart (A ∘ f p) (L p) js) ps := by
  let H := fold 𝒮 Zₐ A
  let T := fun p => leafPartitionExpr (f p) (L p) js
  let G := fun p => js.flatMap (L p)
  let C₀ := fun p => (T p).leaves
  let C₁ := fun p => (G p).map (f p)
  let a := congrArg H (GridExpr.leaves_over T ps)
  let d := fun p => leafPartition_leaves (f p) (L p) js
  let b := congrArg H (congrArg (fun k => ps.flatMap k) (funext d))
  let s := fun p => compressGrid A (T p)
  let h := fun p => eqToHom (leafPartition_eval A (f p) (L p) js)
  let c := fun p => eqToHom (congrArg H (d p))
  let r := fun p => eqToHom (std_fold_map A (f p) (G p))
  let e := fun p => rowsChart (A ∘ f p) (L p) js
  have h₀ : eqToHom (leafPartitionMatrix_eval A f L ps js) =
      eqToHom (GridExpr.eval_over (S:=𝒮) (Z:=Zₐ) A T ps) ≫ act 𝒮 Zₐ h ps := by
    rw [std_act_eqToHom, eqToHom_trans]
  rw [h₀, ← Category.assoc]
  change (compressGrid A (GridExpr.over T ps) ≫ eqToHom (GridExpr.eval_over (S:=𝒮) (Z:=Zₐ) A T ps)) ≫
    act 𝒮 Zₐ h ps = _
  rw [compressGrid_over]
  simp only [Category.assoc]
  have hh (p : P) : s p ≫ h p = c p ≫ r p ≫ e p := by
    have g := (reassoc_of% eqToHom_trans (congrArg H (d p)) (std_fold_map A (f p) (G p))) (e p)
    exact (leafPartition_chart A (f p) (L p) js).trans g.symm
  have h₁ : act 𝒮 Zₐ s ps ≫ act 𝒮 Zₐ h ps = act 𝒮 Zₐ c ps ≫ act 𝒮 Zₐ r ps ≫ act 𝒮 Zₐ e ps :=
    (act_seq 𝒮 Zₐ s h ps).trans ((congrArg (fun k => act 𝒮 Zₐ k ps) (funext hh)).trans
      ((act_seq 𝒮 Zₐ c (fun p => r p ≫ e p) ps).symm.trans
        (congrArg (fun k => act 𝒮 Zₐ c ps ≫ k) (act_seq 𝒮 Zₐ r e ps).symm)))
  have h₂ : rowsChart A C₀ ps ≫ act 𝒮 Zₐ c ps = eqToHom b ≫ rowsChart A C₁ ps :=
    rowsChart_rows_congr A d ps
  change eqToHom a ≫ rowsChart A C₀ ps ≫ (act 𝒮 Zₐ s ps ≫ act 𝒮 Zₐ h ps) =
    eqToHom (a.trans b) ≫ (rowsChart A C₁ ps ≫ act 𝒮 Zₐ r ps) ≫ act 𝒮 Zₐ e ps
  rw [h₁, reassoc_of% h₂, reassoc_of% eqToHom_trans a b]
  simp only [Category.assoc]

end RaggedRows

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
