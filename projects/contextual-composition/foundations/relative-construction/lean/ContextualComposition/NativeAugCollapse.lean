module
public import ContextualComposition.NativeEquivalence

@[expose] public section
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v w w'
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "ℙ" => standardPush (C:=C)
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Z" => 𝟙_ C
variable {X : Type w} {Y : Type w'} (A : X → C) (s : Y → X)

theorem std_fold_map (ys : List Y) :
    fold 𝒮 Z A (ys.map s) = fold 𝒮 Z (fun y => A (s y)) ys := by
  induction ys with
  | nil => rfl
  | cons y ys ih => exact congrArg (fun b => A (s y) ⊗ b) ih

theorem flatMap_single_eq_map (ys : List Y) :
    ys.flatMap (fun y => [s y]) = ys.map s := by
  induction ys with
  | nil => rfl
  | cons y ys ih => simpa only [List.flatMap_cons, List.map_cons, List.singleton_append] using
    (congrArg (List.cons (s y)) ih)

set_option backward.isDefEq.respectTransparency false in
theorem rowsChart_mapped_singletons (L : Y → List X) (E : ∀ y, L y = [s y]) (ys : List Y) :
    eqToHom (congrArg (fold 𝒮 Z A)
      (show ys.map s = ys.flatMap L from (flatMap_single_eq_map s ys).symm.trans
        (congrArg (fun J => ys.flatMap J) (funext E).symm))) ≫
      rowsChart A L ys ≫ act 𝒮 Z (fun y =>
        eqToHom (congrArg (fold 𝒮 Z A) (E y)) ≫ (ρ_ (A (s y))).hom) ys =
    eqToHom (std_fold_map A s ys) := by
  have h : L = fun y => [s y] := funext E
  subst L
  simp only [eqToHom_refl, Category.id_comp]
  induction ys with
  | nil =>
    simp only [rowsChart, act, eqToHom_refl, Category.id_comp, fold]
    rfl
  | cons a ys ih =>
    let F := fold 𝒮 Z A
    let p (y : Y) : F [s y] ⟶ A (s y) := (ρ_ (A (s y))).hom
    let l := ys.flatMap (fun y => [s y])
    have e : eqToHom (congrArg F (flatMap_single_eq_map s (a::ys)).symm) =
        A (s a) ◁ eqToHom (congrArg F (flatMap_single_eq_map s ys).symm) := by
      rw [whiskerLeft_eqToHom]
    change eqToHom (congrArg F (flatMap_single_eq_map s (a::ys)).symm) ≫
      (join additiveStructure A [s a] l ≫ (𝟙 (F [s a]) ⊗ₘ rowsChart A (fun y => [s y]) ys)) ≫
        (p a ⊗ₘ act 𝒮 Z p ys) = _
    rw [e, Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]
    let J : F (s a::l) ⟶ F [s a] ⊗ F l := join additiveStructure A [s a] l
    have j : J ≫ (p a ▷ F l) = 𝟙 (A (s a) ⊗ F l) := by
      unfold J p
      rw [std_join_cons, std_join_nil]
      monoidal
    calc
      _ = (A (s a) ◁ eqToHom (congrArg F (flatMap_single_eq_map s ys).symm)) ≫ J ≫
          (p a ▷ F l) ≫ (A (s a) ◁ (rowsChart A (fun y => [s y]) ys ≫ act 𝒮 Z p ys)) := by
        rw [tensorHom_def]
      _ = _ := by
        rw [← Category.assoc J, j]
        change (A (s a) ◁ eqToHom (congrArg F (flatMap_single_eq_map s ys).symm)) ≫
          𝟙 (A (s a) ⊗ F l) ≫
          (A (s a) ◁ (rowsChart A (fun y => [s y]) ys ≫ act 𝒮 Z p ys)) =
            eqToHom (std_fold_map A s (a::ys))
        rw [Category.id_comp, ← whiskerLeft_comp]
        have e' := congrArg (fun q => A (s a) ◁ q) ih
        rw [whiskerLeft_eqToHom] at e'
        exact e'


set_option backward.isDefEq.respectTransparency false in
/-- Collapse the literal singleton fibres of an equivalence inside any
second native direct image. The sum over the second map can itself be
empty, and remains the explicit zero fold in that case. -/
theorem standardPush_equiv_collapse {n m l : Nat}
    (e : Fin n ≃ Fin m) (g : Fin m → Fin l) (A : Fin n → C) (B : Fin m → C)
    (p : ∀ y, A (e.symm y) ⟶ B y) (j : Fin l)
    (r : AddressOrder (Fin n) (fibreList (g ∘ e) j) ((fibreList g j).map e.symm)) :
    standardPushSplit e g A j ≫
      standardPushMap g (fun y => reindexSingleton e A y ≫ p y) j =
    AddressOrder.mapSum additiveStructure A r ≫
      eqToHom (std_fold_map A e.symm (fibreList g j)) ≫ standardPushMap g p j := by
  let ys := fibreList g j
  let L := fibreList e
  let E : ∀ y, L y = [e.symm y] := equiv_fibreList e
  let H : ys.map e.symm = ys.flatMap L := (flatMap_single_eq_map e.symm ys).symm.trans
    (congrArg (fun J => ys.flatMap J) (funext E).symm)
  rw [standardPushSplit_choice e g A j (.seq r (castOrder H))]
  have h : AddressOrder.mapSum additiveStructure A (.seq r (castOrder H)) =
      AddressOrder.mapSum additiveStructure A r ≫ eqToHom (congrArg (fold 𝒮 Z A) H) := by
    change AddressOrder.mapSum additiveStructure A r ≫ AddressOrder.mapSum additiveStructure A
      (castOrder H) = _
    rw [castOrder_map]
  rw [h, standardPushMap_comp]
  have h' : eqToHom (congrArg (fold 𝒮 Z A) H) ≫ rowsChart A L ys ≫
        standardPushMap g (reindexSingleton e A) j =
      eqToHom (std_fold_map A e.symm ys) :=
    rowsChart_mapped_singletons A e.symm L E ys
  simp only [Category.assoc]
  have k := congrArg (fun t => AddressOrder.mapSum additiveStructure A r ≫ t ≫ standardPushMap g p j) h'
  simp only [Category.assoc] at k
  exact k

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
