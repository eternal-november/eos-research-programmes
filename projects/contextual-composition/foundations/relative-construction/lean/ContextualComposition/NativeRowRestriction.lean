module
public import ContextualComposition.NativeAttachParent

@[expose] public section
/-! The ordered native row chart under relabeling and restriction. A
block selector changes positions, not the underlying fibre arrows. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v w w'
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Z" => 𝟙_ C
variable {X : Type w} {Y : Type w'} (A : X → C) (f : Y → X)

theorem fold_map_append {xs ys : List Y} :
    fold 𝒮 Z A (xs.map f ++ ys.map f) = fold 𝒮 Z (fun y => A (f y)) (xs ++ ys) :=
  (congrArg (fold 𝒮 Z A) (List.map_append (f:=f) (l₁:=xs) (l₂:=ys)).symm).trans
    (std_fold_map A f (xs ++ ys))

set_option backward.isDefEq.respectTransparency false in
theorem join_relabel (xs ys : List Y) :
    join additiveStructure A (xs.map f) (ys.map f) ≫
      (eqToHom (std_fold_map A f xs) ⊗ₘ eqToHom (std_fold_map A f ys)) =
    eqToHom (fold_map_append A f (xs:=xs) (ys:=ys)) ≫
      join additiveStructure (fun y => A (f y)) xs ys := by
  induction xs with
  | nil =>
    let q := eqToHom (std_fold_map A f ys)
    change (λ_ _).inv ≫ (𝟙 Z ⊗ₘ q) = q ≫ (λ_ _).inv
    rw [id_tensorHom, leftUnitor_inv_naturality]
  | cons x xs ih =>
    let a := A (f x)
    let L := fold 𝒮 Z A (xs.map f)
    let R := fold 𝒮 Z A (ys.map f)
    let L' := fold 𝒮 Z (fun y => A (f y)) xs
    let R' := fold 𝒮 Z (fun y => A (f y)) ys
    let p : L ⟶ L' := eqToHom (std_fold_map A f xs)
    let q : R ⟶ R' := eqToHom (std_fold_map A f ys)
    let j : fold 𝒮 Z A (xs.map f ++ ys.map f) ⟶ L ⊗ R :=
      join additiveStructure A (xs.map f) (ys.map f)
    let j' : fold 𝒮 Z (fun y => A (f y)) (xs ++ ys) ⟶ L' ⊗ R' :=
      join additiveStructure (fun y => A (f y)) xs ys
    let r := eqToHom (fold_map_append A f (xs:=xs) (ys:=ys))
    have e : eqToHom (fold_map_append A f (xs:=x::xs) (ys:=ys)) = a ◁ r := by
      rw [whiskerLeft_eqToHom]
    have e' : join additiveStructure A ((x::xs).map f) (ys.map f) = (a ◁ j) ≫ (α_ a L R).inv :=
      std_join_cons A (f x) (xs.map f) (ys.map f)
    rw [e']
    simp only [std_join_cons, std_fold_map_cons]
    rw [e]
    change ((a ◁ j) ≫ (α_ a L R).inv) ≫ ((a ◁ p) ⊗ₘ q) =
      (a ◁ r) ≫ (a ◁ j') ≫ (α_ a L' R').inv
    have h := associator_inv_naturality (𝟙 a) p q
    rw [id_tensorHom, id_tensorHom] at h
    have H : j ≫ (p ⊗ₘ q) = r ≫ j' := ih
    rw [Category.assoc, ← h, ← whiskerLeft_comp_assoc, H, whiskerLeft_comp, Category.assoc]


section Rows
variable {V : Type*} (L : V → List Y)
set_option quotPrecheck false in
local notation "M" => fun y => (L y).map f
local notation "G" => fun x => A (f x)
local notation "F" => fold 𝒮 Z A
local notation "P" => fold 𝒮 Z G

theorem rows_relabel_obj (ys : List V) :
    F (ys.flatMap M) = P (ys.flatMap L) :=
  (congrArg F (List.map_flatMap (f:=f) (g:=L) (l:=ys)).symm).trans
    (std_fold_map A f (ys.flatMap L))

set_option backward.isDefEq.respectTransparency false in
theorem rowsChart_relabel_input (ys : List V) :
    rowsChart A M ys ≫ act 𝒮 Z (fun y => eqToHom (std_fold_map A f (L y))) ys =
      eqToHom (rows_relabel_obj A f L ys) ≫ rowsChart G L ys := by
  induction ys with
  | nil =>
    change 𝟙 Z ≫ 𝟙 Z = 𝟙 Z ≫ 𝟙 Z
    rfl
  | cons y ys ih =>
    let x := L y
    let l := ys.flatMap L
    let m := ys.flatMap M
    let e : m = l.map f := (List.map_flatMap (f:=f) (g:=L) (l:=ys)).symm
    let d : F (x.map f ++ m) = F (x.map f ++ l.map f) :=
      congrArg F (congrArg (fun t => x.map f ++ t) e)
    let s : F m = F (l.map f) := congrArg F e
    let t : F (l.map f) = P l := std_fold_map A f l
    let x' : F (x.map f) = P x := std_fold_map A f x
    let j : F (x.map f ++ m) ⟶ F (x.map f) ⊗ F m := join additiveStructure A (x.map f) m
    let j' : F (x.map f ++ l.map f) ⟶ F (x.map f) ⊗ F (l.map f) :=
      join additiveStructure A (x.map f) (l.map f)
    let j₀ : P (x ++ l) ⟶ P x ⊗ P l := join additiveStructure G x l
    let J : F (x.map f ++ l.map f) = P (x ++ l) := fold_map_append A f (xs:=x) (ys:=l)
    let k := rowsChart A M ys
    let k' := rowsChart G L ys
    let r := act 𝒮 Z (fun j => eqToHom (std_fold_map A f (L j))) ys
    change (j ≫ (𝟙 (F (x.map f)) ⊗ₘ k)) ≫ (eqToHom x' ⊗ₘ r) =
      eqToHom (d.trans J) ≫ (j₀ ≫ (𝟙 (P x) ⊗ₘ k'))
    have p : k ≫ r = eqToHom (s.trans t) ≫ k' := ih
    have h : eqToHom d ≫ j' = j ≫ F (x.map f) ◁ eqToHom s :=
      join_tail_congr A (x.map f) e
    have g : j' ≫ (eqToHom x' ⊗ₘ eqToHom t) = eqToHom J ≫ j₀ :=
      join_relabel A f x l
    rw [Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, p,
      ← eqToHom_trans s t]
    have f₀ : (eqToHom x' ⊗ₘ eqToHom s ≫ eqToHom t ≫ k') =
        (F (x.map f) ◁ eqToHom s) ≫ (eqToHom x' ⊗ₘ eqToHom t) ≫ (𝟙 (P x) ⊗ₘ k') := by
      rw [← id_tensorHom, tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom,
        Category.id_comp, Category.comp_id]
      rw [Category.assoc (eqToHom s)]
    rw [Category.assoc (eqToHom s), f₀, ← Category.assoc j, ← h]
    simp only [Category.assoc]
    rw [reassoc_of% g, ← Category.assoc (eqToHom d), eqToHom_trans]


set_option backward.isDefEq.respectTransparency false in
theorem rowsChart_relabel_input_inv {M' : V → List X} (hs : ∀ y, (L y).map f = M' y)
    (ys : List V) :
    rowsChart G L ys ≫
      act 𝒮 Z (fun y => eqToHom ((std_fold_map A f (L y)).symm.trans (congrArg F (hs y)))) ys =
    eqToHom ((std_fold_map A f (ys.flatMap L)).symm.trans
      (congrArg F ((List.map_flatMap (f:=f) (g:=L) (l:=ys)).trans
        (congrArg (fun Q => ys.flatMap Q) (funext hs))))) ≫ rowsChart A M' ys := by
  have e : M' = fun y => (L y).map f := (funext hs).symm
  subst M'
  let U := fun y => fold 𝒮 Z G (L y)
  let V' := fun y => fold 𝒮 Z A ((L y).map f)
  let p (y : V) : V' y = U y := std_fold_map A f (L y)
  let c := eqToHom (rows_relabel_obj A f L ys)
  let d := eqToHom (rows_relabel_obj A f L ys).symm
  let r := rowsChart A M ys
  let s := rowsChart G L ys
  let Mup := act 𝒮 Z (fun y => eqToHom (p y)) ys
  let Mdown := act 𝒮 Z (fun y => eqToHom (p y).symm) ys
  have h : r ≫ Mup = c ≫ s := rowsChart_relabel_input A f L ys
  have i : d ≫ c = 𝟙 _ := by unfold d c; rw [eqToHom_trans]; rfl
  have j : Mup ≫ Mdown = 𝟙 _ := by
    change (act 𝒮 Z (fun y => eqToHom (p y)) ys) ≫
        act 𝒮 Z (fun y => eqToHom (p y).symm) ys = _
    have k : (fun y => eqToHom (p y) ≫ eqToHom (p y).symm) = fun y => 𝟙 (V' y) := by
      funext y
      rw [eqToHom_trans]
      rfl
    have E := act_seq 𝒮 Z (fun y => eqToHom (p y)) (fun y => eqToHom (p y).symm) ys
    change _ ≫ _ = _ at E
    rw [k] at E
    exact E.trans (occurrence_act_id V' ys)
  have k := congrArg (fun t => d ≫ t ≫ Mdown) h
  change s ≫ Mdown = d ≫ r
  simp only [Category.assoc, j, reassoc_of% i] at k
  exact k.symm.trans (congrArg (fun q => d ≫ q) (Category.comp_id r))

end Rows

section RowIndices
variable {V W : Type*} (L : V → List X) (g : W → V)
set_option backward.isDefEq.respectTransparency false in
theorem rowsChart_relabel_index (ys : List W) :
    rowsChart A L (ys.map g) ≫
      eqToHom (std_fold_map (fun y => fold 𝒮 Z A (L y)) g ys) =
      eqToHom (congrArg (fold 𝒮 Z A) (List.flatMap_map g L ys)) ≫
        rowsChart A (L ∘ g) ys := by
  induction ys with
  | nil =>
    change 𝟙 Z ≫ 𝟙 Z = 𝟙 Z ≫ 𝟙 Z
    rfl
  | cons y ys ih =>
    let F := fold 𝒮 Z A
    let B := fun y => F (L y)
    let a := L (g y)
    let b := (ys.map g).flatMap L
    let c := ys.flatMap (L ∘ g)
    let e : b = c := List.flatMap_map g L ys
    let d := congrArg F (congrArg (fun l => a ++ l) e)
    let J : F (a ++ b) ⟶ F a ⊗ F b := join additiveStructure A a b
    let J' : F (a ++ c) ⟶ F a ⊗ F c := join additiveStructure A a c
    let s := rowsChart A L (ys.map g)
    let t := rowsChart A (L ∘ g) ys
    let U := F a
    let h := eqToHom (std_fold_map B g ys)
    have e₀ : eqToHom (std_fold_map B g (y::ys)) = U ◁ h :=
      std_fold_map_cons B g y ys
    have e₁ : eqToHom d ≫ J' = J ≫ U ◁ eqToHom (congrArg F e) := join_tail_congr A a e
    have e₂ : s ≫ h = eqToHom (congrArg F e) ≫ t := ih
    rw [e₀]
    change (J ≫ (𝟙 U ⊗ₘ s)) ≫ U ◁ h = eqToHom d ≫ J' ≫ (𝟙 U ⊗ₘ t)
    rw [id_tensorHom, id_tensorHom, Category.assoc, ← whiskerLeft_comp, e₂,
      whiskerLeft_comp, ← Category.assoc, ← e₁, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
theorem rowsChart_relabel_index_inv (ys : List W) :
    rowsChart A (L ∘ g) ys ≫
      eqToHom (std_fold_map (fun y => fold 𝒮 Z A (L y)) g ys).symm =
      eqToHom (congrArg (fold 𝒮 Z A) (List.flatMap_map g L ys).symm) ≫
        rowsChart A L (ys.map g) := by
  let e := eqToHom (congrArg (fold 𝒮 Z A) (List.flatMap_map g L ys))
  let e' := eqToHom (congrArg (fold 𝒮 Z A) (List.flatMap_map g L ys).symm)
  let f := eqToHom (std_fold_map (fun y => fold 𝒮 Z A (L y)) g ys)
  let f' := eqToHom (std_fold_map (fun y => fold 𝒮 Z A (L y)) g ys).symm
  have a : e' ≫ e = 𝟙 _ := by unfold e' e; rw [eqToHom_trans]; rfl
  have b : f ≫ f' = 𝟙 _ := by unfold f' f; rw [eqToHom_trans]; rfl
  let r := rowsChart A L (ys.map g)
  let s := rowsChart A (L ∘ g) ys
  have k : r ≫ f = e ≫ s := rowsChart_relabel_index A L g ys
  have h := congrArg (fun t => e' ≫ t ≫ f') k
  change s ≫ f' = e' ≫ r
  simp only [Category.assoc, b, reassoc_of% a, Category.comp_id] at h
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
theorem rowsChart_index_apply {B : V → C} (p : ∀ v, fold 𝒮 Z A (L v) ⟶ B v)
    (is : List W) {ys : List V} (m : is.map g = ys) :
    rowsChart A (L ∘ g) is ≫ act 𝒮 Z (fun x => p (g x)) is ≫
      eqToHom ((std_fold_map B g is).symm.trans (congrArg (fold 𝒮 Z B) m)) =
    eqToHom (congrArg (fold 𝒮 Z A) ((List.flatMap_map g L is).symm.trans
      (congrArg (fun xs => xs.flatMap L) m))) ≫
      rowsChart A L ys ≫ act 𝒮 Z p ys := by
  subst ys
  let X := fun v => fold 𝒮 Z A (L v)
  let j := eqToHom (std_fold_map X g is)
  let j' := eqToHom (std_fold_map X g is).symm
  let b := eqToHom (std_fold_map B g is)
  let b' := eqToHom (std_fold_map B g is).symm
  let r := rowsChart A (L ∘ g) is
  let s := act 𝒮 Z (fun x => p (g x)) is
  let t := act 𝒮 Z p (is.map g)
  let k := rowsChart A L (is.map g)
  let a := eqToHom (congrArg (fold 𝒮 Z A) (List.flatMap_map g L is).symm)
  have e : j' ≫ j = 𝟙 _ := by unfold j j'; rw [eqToHom_trans]; rfl
  have e' : b ≫ b' = 𝟙 _ := by unfold b b'; rw [eqToHom_trans]; rfl
  have h : j ≫ s = t ≫ b := std_act_map X g p is
  have h' : r ≫ j' = a ≫ k := rowsChart_relabel_index_inv A L g is
  have d := congrArg (fun q => j' ≫ q ≫ b') h
  simp only [Category.assoc, e', reassoc_of% e, Category.comp_id] at d
  change r ≫ s ≫ b' = a ≫ k ≫ t
  rw [d, ← Category.assoc, h', Category.assoc]
end RowIndices
end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
