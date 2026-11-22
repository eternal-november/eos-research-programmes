module
public import ContextualComposition.NativeIndependentTerminal
@[expose] public section
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v w
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
variable {X Y I J : Type w}

def partitionedPairJointExpr (rows : I → List X) (cols : J → List Y) (is : List I) (js : List J) :
    GridExpr (X × Y) :=
  GridExpr.over (fun i => GridExpr.over (fun j => rectPairExpr (rows i) (cols j)) js) is

theorem partitionedPairJoint_leaves (rows : I → List X) (cols : J → List Y)
    (is : List I) (js : List J) :
    (partitionedPairJointExpr rows cols is js).leaves =
      (is.product js).flatMap (fun t => (rows t.1).product (cols t.2)) := by
  unfold partitionedPairJointExpr
  rw [GridExpr.leaves_over]
  change _ = (is.flatMap (fun i => js.map (fun j => (i,j)))).flatMap _
  rw [List.flatMap_assoc]
  apply congrArg (fun q => is.flatMap q)
  funext i
  rw [GridExpr.leaves_over, List.flatMap_map]
  exact congrArg (fun q => js.flatMap q) (funext (fun j => rectPairExpr_leaves (rows i) (cols j)))

theorem partitionedPairJoint_eval (A : X × Y → C) (rows : I → List X) (cols : J → List Y)
    (is : List I) (js : List J) :
    GridExpr.eval (S:=𝒮) (Z:=Zₐ) A (partitionedPairJointExpr rows cols is js) =
      fold 𝒮 Zₐ (fun i => fold 𝒮 Zₐ
        (fun j => fold 𝒮 Zₐ (fun x => fold 𝒮 Zₐ (fun y => A (x,y)) (cols j)) (rows i)) js) is := by
  unfold partitionedPairJointExpr
  rw [GridExpr.eval_over]
  congr 1
  funext i
  rw [GridExpr.eval_over]
  congr 1
  funext j
  exact rectPairExpr_eval A (rows i) (cols j)

set_option backward.isDefEq.respectTransparency false in
theorem partitionedPairJoint_chart (A : X × Y → C) (rows : I → List X) (cols : J → List Y)
    (is : List I) (js : List J) (H : I × J → C)
    (p : ∀ t, fold 𝒮 Zₐ (fun x => fold 𝒮 Zₐ (fun y => A (x,y)) (cols t.2)) (rows t.1) ⟶ H t) :
    compressGrid A (partitionedPairJointExpr rows cols is js) ≫
      eqToHom (partitionedPairJoint_eval A rows cols is js) ≫
      act 𝒮 Zₐ (fun i => act 𝒮 Zₐ (fun j => p (i,j)) js) is =
    eqToHom (congrArg (fold 𝒮 Zₐ A) (partitionedPairJoint_leaves rows cols is js)) ≫
      rowsChart A (fun t : I × J => (rows t.1).product (cols t.2)) (is.product js) ≫
      act 𝒮 Zₐ (fun t => rectWordChart A (rows t.1) (cols t.2) ≫ p t) (is.product js) ≫ rectWordChart H is js := by
  let P := fun t : I × J => rectPairExpr (rows t.1) (cols t.2)
  let L := fun t => (P t).leaves
  let L' := fun t : I × J => (rows t.1).product (cols t.2)
  let F := fold 𝒮 Zₐ A
  let r := fun t : I × J => rectPairExpr_eval A (rows t.1) (cols t.2)
  let c := fun t : I × J => eqToHom (congrArg F (rectPairExpr_leaves (rows t.1) (cols t.2)))
  let u := fun t : I × J => rectWordChart A (rows t.1) (cols t.2) ≫ p t
  let g := fun t : I × J => eqToHom (r t) ≫ p t
  let w := is.product js
  have h (t : I × J) : compressGrid A (P t) ≫ g t = c t ≫ u t := by
    have h := congrArg (fun z => z ≫ p t) (rectPairExpr_chart A (rows t.1) (cols t.2))
    simpa only [Category.assoc] using h
  have b := compressGrid_pair_context_post A P is js H g
  dsimp only at b
  let M := fun i => GridExpr.over (fun j => P (i,j)) js
  let e : (GridExpr.over M is).leaves = w.flatMap L :=
    (GridExpr.leaves_over M is).trans ((congrArg (fun k => is.flatMap k)
      (funext fun i => GridExpr.leaves_over (fun j => P (i,j)) js)).trans
        ((List.flatMap_assoc (l:=is) (f:=fun i => js.map (fun j => (i,j))) (g:=L)).trans
          (congrArg (fun k => is.flatMap k) (funext fun i => List.flatMap_map (fun j => (i,j)) L js))).symm)
  let E := (GridExpr.eval_over A M is).trans (congrArg (fun k => fold 𝒮 Zₐ k is)
      (funext fun i => GridExpr.eval_over A (fun j => P (i,j)) js))
  let z := fun i => act 𝒮 Zₐ (fun j => eqToHom (r (i,j))) js
  have z₁ : eqToHom (partitionedPairJoint_eval A rows cols is js) =
      eqToHom E ≫ act 𝒮 Zₐ z is := by
    have hz (i : I) : z i = eqToHom (congrArg (fun B => fold 𝒮 Zₐ B js) (funext fun j => r (i,j))) := std_act_eqToHom _ _
    rw [show z = _ from funext hz, std_act_eqToHom, eqToHom_trans]
  have h₀ (i : I) : z i ≫ act 𝒮 Zₐ (fun j => p (i,j)) js = act 𝒮 Zₐ (fun j => g (i,j)) js :=
    act_seq 𝒮 Zₐ _ _ js
  have h₁ : (act 𝒮 Zₐ z is ≫ act 𝒮 Zₐ (fun i => act 𝒮 Zₐ (fun j => p (i,j)) js) is) =
      act 𝒮 Zₐ (fun i => act 𝒮 Zₐ (fun j => g (i,j)) js) is :=
    (act_seq 𝒮 Zₐ _ _ is).trans (congrArg (fun h => act 𝒮 Zₐ h is) (funext h₀))
  rw [z₁]
  simp only [Category.assoc]
  change compressGrid A (GridExpr.over M is) ≫ eqToHom E ≫
    (act 𝒮 Zₐ z is ≫ act 𝒮 Zₐ (fun i => act 𝒮 Zₐ (fun j => p (i,j)) js) is) = _
  rw [h₁]
  rw [b]
  let d := congrArg F (congrArg (fun k => w.flatMap k) (funext (fun t : I × J => rectPairExpr_leaves (rows t.1) (cols t.2))))
  have f := rowsChart_rows_congr A (fun t : I × J => rectPairExpr_leaves (rows t.1) (cols t.2)) w
  have s := (congrArg (fun q => act 𝒮 Zₐ q w) (funext h)).trans (act_seq 𝒮 Zₐ c u w).symm
  change eqToHom (congrArg F e) ≫ rowsChart A L w ≫ act 𝒮 Zₐ (fun t => compressGrid A (P t) ≫ g t) w ≫ rectWordChart H is js = _
  rw [reassoc_of% s]
  rw [reassoc_of% f]
  change eqToHom (congrArg F e) ≫ eqToHom d ≫ rowsChart A L' w ≫ act 𝒮 Zₐ u w ≫ rectWordChart H is js =
    eqToHom ((congrArg F e).trans d) ≫ rowsChart A L' w ≫ act 𝒮 Zₐ u w ≫ rectWordChart H is js
  rw [reassoc_of% eqToHom_trans]


def partitionedPairRowExpr (x : X) (cols : J → List Y) (js : List J) : GridExpr (X × Y) :=
  GridExpr.over (fun j => GridExpr.over (fun y => .leaf (x,y)) (cols j)) js

theorem partitionedPairRow_leaves (x : X) (cols : J → List Y) (js : List J) :
    (partitionedPairRowExpr x cols js).leaves = (js.flatMap cols).map (fun y => (x,y)) := by
  unfold partitionedPairRowExpr
  rw [GridExpr.leaves_over, List.map_flatMap]
  exact congrArg (fun k => js.flatMap k) (funext fun j => leafWord_pin (fun y => (x,y)) (cols j))

theorem partitionedPairRow_eval (A : X × Y → C) (x : X) (cols : J → List Y) (js : List J) :
    GridExpr.eval (S:=𝒮) (Z:=Zₐ) A (partitionedPairRowExpr x cols js) =
      fold 𝒮 Zₐ (fun j => fold 𝒮 Zₐ (fun y => A (x,y)) (cols j)) js := by
  unfold partitionedPairRowExpr
  rw [GridExpr.eval_over]
  congr 1
  funext j
  exact GridExpr.eval_over _ _ _

set_option backward.isDefEq.respectTransparency false in
theorem partitionedPairRow_chart (A : X × Y → C) (x : X) (cols : J → List Y) (js : List J) :
    compressGrid A (partitionedPairRowExpr x cols js) ≫
      eqToHom (partitionedPairRow_eval A x cols js) =
    eqToHom ((congrArg (fold 𝒮 Zₐ A) (partitionedPairRow_leaves x cols js)).trans
      (std_fold_map A (fun y => (x,y)) (js.flatMap cols))) ≫
      rowsChart (fun y => A (x,y)) cols js := by
  let f := fun y : Y => (x,y)
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
  have e : eqToHom (partitionedPairRow_eval A x cols js) =
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
  have h₂ : R' ≫ act 𝒮 Zₐ z js = k ≫ rowsChart (fun y => A (x,y)) cols js :=
    rowsChart_relabel_input A f cols js
  let π := congrArg F (GridExpr.leaves_over P js)
  change a ≫ R ≫ (act 𝒮 Zₐ p js ≫ act 𝒮 Zₐ c js) =
    eqToHom ((π.trans e₀).trans e₁) ≫ rowsChart (fun y => A (x,y)) cols js
  rw [h₀, reassoc_of% h₁, h₂]
  change eqToHom π ≫ eqToHom e₀ ≫ eqToHom e₁ ≫ rowsChart (fun y => A (x,y)) cols js = _
  rw [reassoc_of% eqToHom_trans π e₀, reassoc_of% eqToHom_trans (π.trans e₀) e₁]


def partitionedPairOccurrenceExpr (rows : I → List X) (cols : J → List Y) (is : List I) (js : List J) :
    GridExpr (X × Y) :=
  GridExpr.over (fun i => GridExpr.over (fun x => partitionedPairRowExpr x cols js) (rows i)) is

theorem partitionedPairOccurrence_leaves (rows : I → List X) (cols : J → List Y)
    (is : List I) (js : List J) :
    (partitionedPairOccurrenceExpr rows cols is js).leaves = (is.flatMap rows).product (js.flatMap cols) := by
  unfold partitionedPairOccurrenceExpr
  rw [GridExpr.leaves_over]
  change _ = (is.flatMap rows).flatMap (fun x => (js.flatMap cols).map (fun y => (x,y)))
  rw [List.flatMap_assoc]
  apply congrArg (fun q => is.flatMap q)
  funext i
  rw [GridExpr.leaves_over]
  exact congrArg (fun q => (rows i).flatMap q) (funext (fun x => partitionedPairRow_leaves x cols js))

theorem partitionedPairOccurrence_eval (A : X × Y → C) (rows : I → List X) (cols : J → List Y)
    (is : List I) (js : List J) :
    GridExpr.eval (S:=𝒮) (Z:=Zₐ) A (partitionedPairOccurrenceExpr rows cols is js) =
      fold 𝒮 Zₐ (fun i => fold 𝒮 Zₐ
        (fun x => fold 𝒮 Zₐ (fun j => fold 𝒮 Zₐ (fun y => A (x,y)) (cols j)) js) (rows i)) is := by
  unfold partitionedPairOccurrenceExpr
  rw [GridExpr.eval_over]
  congr 1
  funext i
  rw [GridExpr.eval_over]
  congr 1
  funext x
  exact partitionedPairRow_eval A x cols js

set_option backward.isDefEq.respectTransparency false in
theorem partitionedPairOccurrence_chart (A : X × Y → C) (rows : I → List X) (cols : J → List Y)
    (is : List I) (js : List J) :
    compressGrid A (partitionedPairOccurrenceExpr rows cols is js) ≫
      eqToHom (partitionedPairOccurrence_eval A rows cols is js) =
    eqToHom (congrArg (fold 𝒮 Zₐ A) (partitionedPairOccurrence_leaves rows cols is js)) ≫
      rectWordChart A (is.flatMap rows) (js.flatMap cols) ≫
      act 𝒮 Zₐ (fun x => rowsChart (fun y => A (x,y)) cols js) (is.flatMap rows) ≫
      rowsChart (fun x => fold 𝒮 Zₐ (fun j => fold 𝒮 Zₐ (fun y => A (x,y)) (cols j)) js) rows is := by
  let P := fun x : X => partitionedPairRowExpr x cols js
  let L := fun x => (P x).leaves
  let B := fun x => GridExpr.eval (S:=𝒮) (Z:=Zₐ) A (P x)
  let B' := fun x => fold 𝒮 Zₐ (fun j => fold 𝒮 Zₐ (fun y => A (x,y)) (cols j)) js
  let t := is.flatMap rows
  let w := js.flatMap cols
  let L' := fun x : X => w.map (fun y => (x,y))
  let F := fold 𝒮 Zₐ A
  let M := fun i => GridExpr.over P (rows i)
  let d (x : X) : L x = L' x := partitionedPairRow_leaves x cols js
  let d' := fun x => eqToHom (congrArg F (d x))
  let r := fun x => eqToHom (partitionedPairRow_eval A x cols js)
  let s := fun x => compressGrid A (P x)
  let Q := fun x : X => eqToHom (std_fold_map A (fun y => (x,y)) w)
  let q := fun x : X => rowsChart (fun y => A (x,y)) cols js
  let g := (GridExpr.eval_over A M is).trans (congrArg (fun k => fold 𝒮 Zₐ k is)
    (funext fun i => GridExpr.eval_over A P (rows i)))
  let e : (GridExpr.over M is).leaves = t.flatMap L :=
    (GridExpr.leaves_over M is).trans ((congrArg (fun k => is.flatMap k)
      (funext fun i => GridExpr.leaves_over P (rows i))).trans List.flatMap_assoc.symm)
  let U := eqToHom (congrArg F e)
  let V := eqToHom (congrArg F (congrArg (fun k => t.flatMap k) (funext d)))
  let E := fun i => act 𝒮 Zₐ r (rows i)
  have h₀ : eqToHom (partitionedPairOccurrence_eval A rows cols is js) =
      eqToHom g ≫ act 𝒮 Zₐ E is := by
    have h (i : I) : E i = eqToHom (congrArg (fun a => fold 𝒮 Zₐ a (rows i))
        (funext (fun x => partitionedPairRow_eval A x cols js))) := std_act_eqToHom _ _
    rw [show E = _ from funext h, std_act_eqToHom, eqToHom_trans]
  have h₁ := compressGrid_partition_context A P rows is
  dsimp only at h₁
  have h₂ : rowsChart B rows is ≫ act 𝒮 Zₐ E is = act 𝒮 Zₐ r t ≫ rowsChart B' rows is :=
    (rowsChart_natural rows r is).symm
  have h₃ (x : X) : s x ≫ r x = d' x ≫ Q x ≫ q x := by
    have h := partitionedPairRow_chart A x cols js
    have z := (reassoc_of% eqToHom_trans (congrArg F (d x)) (std_fold_map A (fun y => (x,y)) w)) (q x)
    exact h.trans z.symm
  have h₄ : (act 𝒮 Zₐ s t ≫ act 𝒮 Zₐ r t) = act 𝒮 Zₐ d' t ≫ act 𝒮 Zₐ Q t ≫ act 𝒮 Zₐ q t :=
    (act_seq 𝒮 Zₐ s r t).trans ((congrArg (fun k => act 𝒮 Zₐ k t) (funext h₃)).trans
      ((act_seq 𝒮 Zₐ d' (fun x => Q x ≫ q x) t).symm.trans
        (congrArg (fun k => act 𝒮 Zₐ d' t ≫ k) (act_seq 𝒮 Zₐ Q q t).symm)))
  have h₅ : rowsChart A L t ≫ act 𝒮 Zₐ d' t = V ≫ rowsChart A L' t := rowsChart_rows_congr A d t
  rw [h₀, ← Category.assoc]
  change (compressGrid A (GridExpr.over M is) ≫ eqToHom g) ≫ act 𝒮 Zₐ E is = _
  rw [h₁]
  simp only [Category.assoc]
  change U ≫ rowsChart A L t ≫ act 𝒮 Zₐ s t ≫ (rowsChart B rows is ≫ act 𝒮 Zₐ E is) = _
  rw [h₂, ← Category.assoc (act 𝒮 Zₐ s t), h₄]
  simp only [Category.assoc]
  rw [reassoc_of% h₅]
  let d₀ := congrArg F e
  let d₁ := congrArg F (congrArg (fun k => t.flatMap k) (funext d))
  change eqToHom d₀ ≫ eqToHom d₁ ≫ rowsChart A L' t ≫ act 𝒮 Zₐ Q t ≫ act 𝒮 Zₐ q t ≫ rowsChart B' rows is =
    eqToHom (d₀.trans d₁) ≫ (rowsChart A L' t ≫ act 𝒮 Zₐ Q t) ≫ act 𝒮 Zₐ q t ≫ rowsChart B' rows is
  simp only [Category.assoc]
  rw [reassoc_of% eqToHom_trans d₀ d₁]

def partitionedPairExchange (rows : I → List X) (cols : J → List Y)
    (is : List I) (js : List J) :
    GridCircuit (X × Y) (partitionedPairOccurrenceExpr rows cols is js) (partitionedPairJointExpr rows cols is js) :=
  GridCircuit.foreach _ _ (fun i => GridCircuit.transpose
    (fun (x : X) (j : J) => GridExpr.over (fun y : Y => GridExpr.leaf (x,y)) (cols j)) js (rows i)) is

set_option backward.isDefEq.respectTransparency false in
theorem partitionedPairExchange_eval (A : X × Y → C) (rows : I → List X) (cols : J → List Y)
    (is : List I) (js : List J) :
    HEq (GridCircuit.eval (symmetricCross (C:=C)) A (partitionedPairExchange rows cols is js))
      (act 𝒮 Zₐ (fun i => transposeBlock (symmetricCross (C:=C))
        (fun x j => fold 𝒮 Zₐ (fun y => A (x,y)) (cols j)) js (rows i)) is) := by
  let P := fun (x : X) (j : J) => GridExpr.over (fun y => .leaf (x,y)) (cols j)
  let M := symmetricCross (C:=C)
  let a := fun i => GridExpr.over (fun x => partitionedPairRowExpr x cols js) (rows i)
  let b := fun i => GridExpr.over (fun j => rectPairExpr (rows i) (cols j)) js
  let p := fun i => GridCircuit.transpose P js (rows i)
  have H := GridCircuit.foreach_eval M A a b p is
  apply H.trans
  let G := fun (x : X) (j : J) => fold 𝒮 Zₐ (fun y => A (x,y)) (cols j)
  have E : (fun x j => GridExpr.eval (S:=𝒮) (Z:=Zₐ) A (P x j)) = G := by
    funext x j
    exact GridExpr.eval_over _ _ _
  have p₀ (i : I) : HEq (GridCircuit.eval M A (p i)) (transposeBlock M G js (rows i)) := by
    have q := GridCircuit.transpose_eval M A P js (rows i)
    have h (U V : X → J → C) (e : U = V) :
        HEq (transposeBlock M U js (rows i)) (transposeBlock M V js (rows i)) := by cases e; rfl
    exact q.trans (h _ _ E)
  refine act_heq ?_ ?_ p₀ is
  · funext i
    change GridExpr.eval (S:=𝒮) (Z:=Zₐ) A (a i) = _
    unfold a
    rw [GridExpr.eval_over]
    congr 1
    funext x
    exact partitionedPairRow_eval A x cols js
  · funext i
    change GridExpr.eval (S:=𝒮) (Z:=Zₐ) A (b i) = _
    unfold b
    rw [GridExpr.eval_over]
    congr 1
    funext j
    exact rectPairExpr_eval A (rows i) (cols j)


local notation "MC" => symmetricCross (C:=C)

set_option backward.isDefEq.respectTransparency false in
theorem partitionedPairExchange_gather {T : Bi (coeff (C:=C))}
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ) (N : GridBinary MC R L)
    (A : X → C) (B : Y → C) (rows : I → List X) (cols : J → List Y)
    (is : List I) (js : List J) :
    let a := fun p : X × Y => T.obj (A p.1) (B p.2)
    let o := partitionedPairOccurrenceExpr rows cols is js
    let j := partitionedPairJointExpr rows cols is js
    let t := partitionedPairExchange rows cols is js
    let f := fun i : I => fold 𝒮 Zₐ A (rows i)
    let g := fun j : J => fold 𝒮 Zₐ B (cols j)
    AddressOrder.mapSum additiveStructure a (gridOrder t) ≫
      compressGrid a j ≫ eqToHom (partitionedPairJoint_eval a rows cols is js) ≫
        act 𝒮 Zₐ (fun i => act 𝒮 Zₐ (fun j => rowGather R L A B (rows i) (cols j)) js) is ≫
        rowGather R L f g is js =
    compressGrid a o ≫ eqToHom (partitionedPairOccurrence_eval a rows cols is js) ≫
      independentGroupedGather R L A B rows cols is js := by
  intro a o j t f g
  let P := fun (x : X) (j : J) => fold 𝒮 Zₐ (fun y => a (x,y)) (cols j)
  let m := fun i => transposeBlock MC P js (rows i)
  let n := fun i => act 𝒮 Zₐ (fun j => rowGather R L A B (rows i) (cols j)) js
  let h := fun i => raggedRowGather R L A (rows i) js cols (fun _ => B)
  let w := fun i => raggedColGather R L A (rows i) js cols (fun _ => B)
  let k := rowGather R L f g is js
  let k₀ := DependentFibre.gather R f (fold 𝒮 Zₐ g js) is
  let v := fun i => Lin.collect (Lin.left L (f i)) g js
  have e : GridCircuit.eval MC a t ≫ eqToHom (partitionedPairJoint_eval a rows cols is js) =
      eqToHom (partitionedPairOccurrence_eval a rows cols is js) ≫ act 𝒮 Zₐ m is :=
    heq_paste (partitionedPairOccurrence_eval a rows cols is js)
      (partitionedPairJoint_eval a rows cols is js) (partitionedPairExchange_eval a rows cols is js)
  have e₁ (i : I) : m i ≫ w i = h i := ragged_interchange MC R L N A (rows i) js cols (fun _ => B)
  have e₂ (i : I) : n i ≫ v i = w i := rfl
  have e₃ : k = act 𝒮 Zₐ v is ≫ k₀ := rfl
  have core : act 𝒮 Zₐ m is ≫ act 𝒮 Zₐ n is ≫ k = independentGroupedGather R L A B rows cols is js := by
    rw [e₃, ← Category.assoc (act 𝒮 Zₐ n is)]
    have n₀ := (act_seq 𝒮 Zₐ n v is).trans (congrArg (fun p => act 𝒮 Zₐ p is) (funext e₂))
    refine (congrArg (fun z => act 𝒮 Zₐ m is ≫ z ≫ k₀) n₀).trans ?_
    have h₀ := (act_seq 𝒮 Zₐ m w is).trans (congrArg (fun p => act 𝒮 Zₐ p is) (funext e₁))
    have m₀ := congrArg (fun p => p ≫ k₀) h₀
    change _ = act 𝒮 Zₐ h is ≫ k₀
    simpa only [Category.assoc] using m₀
  have r := compressGrid_order a t
  change AddressOrder.mapSum additiveStructure a (gridOrder t) ≫ compressGrid a j ≫
    eqToHom (partitionedPairJoint_eval a rows cols is js) ≫ act 𝒮 Zₐ n is ≫ k =
      compressGrid a o ≫ eqToHom (partitionedPairOccurrence_eval a rows cols is js) ≫ _
  rw [← Category.assoc (AddressOrder.mapSum additiveStructure a (gridOrder t)), r]
  simp only [Category.assoc]
  rw [reassoc_of% e,core]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
/-- The standard symmetric ordered product chart. The proof compares source
axis grouping with literal target-pair grouping; the input native arrow
cells never enter. -/
theorem independentProduct_sourceChart (T : Bi (coeff (C:=C)))
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    (N : GridBinary MC R L)
    {A B : Family C} {n m : Nat}
    (f : Fin A.n → Fin n) (g : Fin B.n → Fin m)
    (r : AddressOrder (Fin A.n × Fin B.n) (independentWord A B)
      (((List.finRange n).product (List.finRange m)).flatMap (wordFibre (independentWord A B) (Prod.map f g))))
    [∀ x : Fin A.n, (leftFactor T (A.val x)).LaxBraided]
    [rr : (rightFactor (T:=T) (fold 𝒮 Zₐ B.val ((List.finRange m).flatMap (fibreList g)))).LaxBraided]
    [rs : (rightFactor (T:=T)
      (fold 𝒮 Zₐ (fun j => fold 𝒮 Zₐ B.val (fibreList g j)) (List.finRange m))).LaxBraided]
    (hl : ∀ x : Fin A.n, SameLeftGather T (A.val x) L)
    (hr : SameRightGather R (fold 𝒮 Zₐ B.val ((List.finRange m).flatMap (fibreList g))))
    (hr' : SameRightGather R (fold 𝒮 Zₐ (fun j => fold 𝒮 Zₐ B.val (fibreList g j)) (List.finRange m))) :
    IndependentProductSourceChart T R L (A:=A) (B:=B) f g r := by
  let U := fibreList f
  let V := fibreList g
  let xs := List.finRange A.n
  let ys := List.finRange B.n
  let i := List.finRange n
  let j := List.finRange m
  let xw := i.flatMap U
  let yw := j.flatMap V
  let ws := i.product j
  let A₀ := independentLabels T A B
  let F := fold 𝒮 Zₐ A₀
  let Fg := wordFibre (independentWord A B) (Prod.map f g)
  let Fr := fun t : Fin n × Fin m => (U t.1).product (V t.2)
  let P := fun t : Fin n × Fin m => rowGather R L A.val B.val (U t.1) (V t.2)
  let H := fun t : Fin n × Fin m => T.obj (standardPushObj f A.val t.1) (standardPushObj g B.val t.2)
  let D (t : Fin n × Fin m) : Fg t = Fr t :=
    (product_word_fibre xs ys f g t).trans (by
      change (wordFibre xs f t.1).product (wordFibre ys g t.2) =
        (fibreList f t.1).product (fibreList g t.2)
      simp only [xs, ys, wordFibre, fibreList, beq_eq_decide])
  let d := congrArg (fun q => ws.flatMap q) (funext D)
  let c := fun t : Fin n × Fin m => eqToHom (congrArg F (D t))
  let p := fun t : Fin n × Fin m => rectWordChart A₀ (U t.1) (V t.2) ≫ P t
  let ψ := fun t : Fin n × Fin m => (c t ≫ rectWordChart A₀ (U t.1) (V t.2)) ≫ P t
  let G := rowGather R L (standardPushObj f A.val) (standardPushObj g B.val) i j
  let Q := partitionedPairJointExpr U V i j
  let W := partitionedPairOccurrenceExpr U V i j
  let t := partitionedPairExchange U V i j
  let z := partitionedPairJoint_leaves U V i j
  let w := partitionedPairOccurrence_leaves U V i j
  let z' : Q.leaves = ws.flatMap Fg := z.trans d.symm
  let jq := eqToHom (partitionedPairJoint_eval A₀ U V i j)
  let oq := eqToHom (partitionedPairOccurrence_eval A₀ U V i j)
  let At := act 𝒮 Zₐ (fun x => act 𝒮 Zₐ (fun y => P (x,y)) j) i
  let q₀ := rowsChart A₀ Fr ws
  let q₁ := rowsChart A₀ Fg ws
  let q₂ := rectWordChart H i j
  have eact (t : Fin n × Fin m) : ψ t = c t ≫ p t := Category.assoc _ _ _
  have h₁ : act 𝒮 Zₐ ψ ws = act 𝒮 Zₐ c ws ≫ act 𝒮 Zₐ p ws :=
    (congrArg (fun q => act 𝒮 Zₐ q ws) (funext eact)).trans (act_seq 𝒮 Zₐ c p ws).symm
  have h₂ : q₁ ≫ act 𝒮 Zₐ c ws = eqToHom (congrArg F d) ≫ q₀ :=
    rowsChart_rows_congr A₀ D ws
  have hJ : eqToHom (congrArg F z') ≫ q₁ ≫ act 𝒮 Zₐ ψ ws ≫ q₂ =
       compressGrid A₀ Q ≫ jq ≫ At := by
    rw [h₁]
    simp only [Category.assoc]
    rw [reassoc_of% h₂, reassoc_of% eqToHom_trans (congrArg F z') (congrArg F d)]
    exact (partitionedPairJoint_chart A₀ U V i j H P).symm
  let ux := totalPartitionOrder f
  let uy := totalPartitionOrder g
  let o := rectWordAxisOrder ux uy
  let r₀ := ((o.seq (castOrder w.symm)).seq (gridOrder t)).seq (castOrder z')
  have hc : AddressOrder.mapSum additiveStructure A₀ r = AddressOrder.mapSum additiveStructure A₀ r₀ :=
    tagged_permutation_coherent A₀ (independentWord_nodup A B) r r₀
  have hr₀ : AddressOrder.mapSum additiveStructure A₀ r₀ =
      AddressOrder.mapSum additiveStructure A₀ o ≫ eqToHom (congrArg F w.symm) ≫
        AddressOrder.mapSum additiveStructure A₀ (gridOrder t) ≫ eqToHom (congrArg F z') := by
    change ((AddressOrder.mapSum additiveStructure A₀ o ≫ AddressOrder.mapSum additiveStructure A₀ (castOrder w.symm)) ≫
      AddressOrder.mapSum additiveStructure A₀ (gridOrder t)) ≫ AddressOrder.mapSum additiveStructure A₀ (castOrder z') = _
    rw [castOrder_map, castOrder_map]
    simp only [Category.assoc]
  let K := independentGroupedGather R L A.val B.val U V i j
  have e : AddressOrder.mapSum additiveStructure A₀ (gridOrder t) ≫ compressGrid A₀ Q ≫ jq ≫ At ≫ G =
      compressGrid A₀ W ≫ oq ≫ K := partitionedPairExchange_gather R L N A.val B.val U V i j
  let k := fun x => rowsChart (fun y => A₀ (x,y)) V j
  let z₀ := rowsChart (fun x => fold 𝒮 Zₐ (fun j₀ => fold 𝒮 Zₐ (fun y => A₀ (x,y)) (V j₀)) j) U i
  let Rc := rectWordChart A₀ xw yw
  have e₀ : compressGrid A₀ W ≫ oq =
      eqToHom (congrArg F w) ≫ Rc ≫ act 𝒮 Zₐ k xw ≫ z₀ := partitionedPairOccurrence_chart A₀ U V i j
  let Jx := rowsChart A.val U i
  let Jy := rowsChart B.val V j
  let P₀ := AddressOrder.mapSum additiveStructure A.val ux
  let Q₀ := AddressOrder.mapSum additiveStructure B.val uy
  let Rg := rowGather R L A.val B.val xw yw
  let Rs := rowGather R L A.val B.val xs ys
  have e₁ : act 𝒮 Zₐ k xw ≫ z₀ ≫ K = Rg ≫ T.map Jx Jy :=
    @occurrenceFirst_partition C _ _ _ T R L (Fin A.n) (Fin B.n) (Fin n) (Fin m)
      A.val B.val U V i j _ rs hl hr'
  let rY := act 𝒮 Zₐ (fun x => AddressOrder.mapSum additiveStructure (fun y => A₀ (x,y)) uy) xs
  let rX := AddressOrder.mapSum additiveStructure (fun x => fold 𝒮 Zₐ (fun y => A₀ (x,y)) yw) ux
  have e₂ : AddressOrder.mapSum additiveStructure A₀ o ≫ Rc = rectWordChart A₀ xs ys ≫ rY ≫ rX :=
    rectWordChart_axis_order A₀ ux uy
  have e₃ : rY ≫ rX ≫ Rg = Rs ≫ T.map P₀ Q₀ :=
    @independent_gather_order C _ _ _ T R L (Fin A.n) (Fin B.n) A.val B.val xs xw ys yw ux uy _ rr hl hr
  have e₄ : T.map P₀ Q₀ ≫ T.map Jx Jy = T.map (P₀ ≫ Jx) (Q₀ ≫ Jy) := (T.map_seq P₀ Jx Q₀ Jy).symm
  have e₅ : eqToHom (congrArg F w.symm) ≫ eqToHom (congrArg F w) = 𝟙 _ := by
    rw [eqToHom_trans]
    rfl
  unfold IndependentProductSourceChart
  dsimp only
  change AddressOrder.mapSum additiveStructure A₀ r ≫ q₁ ≫ act 𝒮 Zₐ ψ ws ≫ q₂ ≫ G =
    rectWordChart A₀ xs ys ≫ Rs ≫ T.map (P₀ ≫ Jx) (Q₀ ≫ Jy)
  rw [hc, hr₀]
  simp only [Category.assoc]
  rw [reassoc_of% hJ, e]
  rw [reassoc_of% e₀, reassoc_of% e₅, e₁]
  rw [← Category.assoc (AddressOrder.mapSum additiveStructure A₀ o), e₂]
  simp only [Category.assoc]
  rw [reassoc_of% e₃, e₄]

local notation "ℙ" => standardPush (C:=C)

set_option backward.isDefEq.respectTransparency false in
/-- Literal independent product on carrier-changing augmented families.
This uses the actual native product map and proves its augmentation law. -/
noncomputable def independentNativeAugMap (T : Bi (coeff (C:=C)))
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    (N : GridBinary MC R L) (NR : GatherOuterNat R) (NL : GatherLeftNat L)
    {A B A' B' : Family C} {I : C}
    {δ : totalFold A ⟶ I} {η : totalFold B ⟶ I} {δ' : totalFold A' ⟶ I} {η' : totalFold B' ⟶ I}
    (p : AugHom ℙ (totalAug A δ) (totalAug A' δ'))
    (q : AugHom ℙ (totalAug B η) (totalAug B' η'))
    (c : T.obj I I ⟶ I)
    [∀ x : Fin A.n, (leftFactor T (A.val x)).LaxBraided]
    [rr : (rightFactor (T:=T)
      (fold 𝒮 Zₐ B.val ((List.finRange B'.n).flatMap (fibreList q.native.addr)))).LaxBraided]
    [rs : (rightFactor (T:=T)
      (fold 𝒮 Zₐ (fun j => fold 𝒮 Zₐ B.val (fibreList q.native.addr j)) (List.finRange B'.n))).LaxBraided]
    (hl : ∀ x : Fin A.n, SameLeftGather T (A.val x) L)
    (hr : SameRightGather R (fold 𝒮 Zₐ B.val ((List.finRange B'.n).flatMap (fibreList q.native.addr))))
    (hr' : SameRightGather R (fold 𝒮 Zₐ (fun j => fold 𝒮 Zₐ B.val (fibreList q.native.addr j)) (List.finRange B'.n))) :
    AugHom ℙ (independentWordAug T R L A B δ η c) (independentWordAug T R L A' B' δ' η' c) := by
  let p₀ : Hom ℙ A A' := p.native
  let q₀ : Hom ℙ B B' := q.native
  let F := Prod.map p₀.addr q₀.addr
  let w := independentWord A' B'
  let L' := wordFibre (independentWord A B) F
  let f := fun i : Fin w.length => w[i]
  let r := wordNativePartitionOrder F (independent_word_support p₀ q₀) (independentWord_nodup A' B')
  let d : (List.finRange w.length).flatMap (L' ∘ f) = w.flatMap L' :=
    (List.flatMap_map f L' (List.finRange w.length)).symm.trans
      (congrArg (fun k => k.flatMap L') (finRange_get w))
  let z := r.seq (castOrder d)
  have h := @independentProduct_sourceChart C _ _ _ T R L N A B A'.n B'.n p₀.addr q₀.addr z
    _ rr rs hl hr hr'
  exact independentNativeAugMap_of_sourceChart T R L NR NL p q c z h

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
