module
public import ContextualComposition.NativeGatherCoherence

@[expose] public section
/-! Coordinate form of actual native augmentation preservation. The
terminal cell is not a family of maps from separate summands. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "ℙ" => standardPush (C:=C)
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Z" => 𝟙_ C

abbrev totalFold (A : Family C) := fold 𝒮 Z A.val (List.finRange A.n)

noncomputable def totalAug {I : C} (A : Family C) (p : totalFold A ⟶ I) : Aug ℙ I :=
  ⟨A, ⟨terminalCarrier A.n, fun j => eqToHom (congrArg (fold 𝒮 Z A.val)
    (fibreList_terminal A.n j)) ≫ p⟩⟩

noncomputable def totalPartitionOrder {n m : Nat} (f : Fin n → Fin m) :
    AddressOrder (Fin n) (List.finRange n) ((List.finRange m).flatMap (fibreList f)) := by
  let terminal := terminalCarrier m
  let j : Fin 1 := 0
  have h₁ : fibreList (terminal ∘ f) j = List.finRange n := fibreList_terminal _ _
  have h₂ : fibreList terminal j = List.finRange m := fibreList_terminal _ _
  exact .seq (castOrder h₁.symm) (.seq (splitOrder f terminal j)
    (castOrder (congrArg (fun l => l.flatMap (fibreList f)) h₂)))

set_option backward.isDefEq.respectTransparency false in
theorem standardPush_terminal_chart {n m : Nat} (f : Fin n → Fin m) (A : Fin n → C)
    (j : Fin 1) (order : AddressOrder (Fin n) (List.finRange n) ((List.finRange m).flatMap (fibreList f))) :
    standardPushSplit f (terminalCarrier m) A j ≫
      eqToHom (congrArg (fold 𝒮 Z (standardPushObj f A)) (fibreList_terminal m j)) =
      eqToHom (congrArg (fold 𝒮 Z A) (fibreList_terminal n j)) ≫
        AddressOrder.mapSum additiveStructure A order ≫ rowsChart A (fibreList f) (List.finRange m) := by
  let a : fibreList (terminalCarrier m ∘ f) j = List.finRange n := fibreList_terminal _ _
  let b : fibreList (terminalCarrier m) j = List.finRange m := fibreList_terminal _ _
  let c := congrArg (fun l => l.flatMap (fibreList f)) b.symm
  let r := AddressOrder.mapSum additiveStructure A order
  let G := fold 𝒮 Z A
  let H := fold 𝒮 Z (standardPushObj f A)
  rw [standardPushSplit_choice _ _ _ _ (.seq (castOrder a) (.seq order (castOrder c)))]
  have h : AddressOrder.mapSum additiveStructure A ((castOrder a).seq (order.seq (castOrder c))) =
      eqToHom (congrArg G a) ≫ r ≫ eqToHom (congrArg G c) := by
    change AddressOrder.mapSum additiveStructure A (castOrder a) ≫ r ≫
      AddressOrder.mapSum additiveStructure A (castOrder c) = _
    rw [castOrder_map, castOrder_map]
  rw [h]
  have e := rowsChart_list_congr A (fibreList f) b.symm
  have x : eqToHom (congrArg H b.symm) ≫ eqToHom (congrArg H b) = 𝟙 _ := by
    rw [eqToHom_trans]
    rfl
  simp only [Category.assoc]
  rw [reassoc_of% e, x]
  let J : G ((List.finRange m).flatMap (fibreList f)) ⟶ H (List.finRange m) :=
    rowsChart A (fibreList f) (List.finRange m)
  exact congrArg (fun z => eqToHom (congrArg G a) ≫ r ≫ z) (Category.comp_id J)

set_option backward.isDefEq.respectTransparency false in
/-- The law for the native composite into the terminal shape is precisely a
single ordered regrouping, the old whole-fibre cells, then the new whole
augmentation. This law requires no uniqueness assumption on zero-fibre maps. -/
theorem totalAug_preserving_iff {A B : Family C} {I : C}
    (u : Hom ℙ A B) (p : totalFold A ⟶ I) (q : totalFold B ⟶ I) :
    u.comp (totalAug B q).ε = (totalAug A p).ε ↔
      AddressOrder.mapSum additiveStructure A.val (totalPartitionOrder u.addr) ≫
        rowsChart A.val (fibreList u.addr) (List.finRange B.n) ≫
          act 𝒮 Z u.cell (List.finRange B.n) ≫ q = p := by
  refine (native_hom_iff_cell rfl _ _).trans ?_
  constructor <;> intro h
  all_goals
    let f := u.addr
    let P := fun j => eqToHom (congrArg (fold 𝒮 Z A.val) (fibreList_terminal A.n j))
    let Q := fun j => eqToHom (congrArg (fold 𝒮 Z B.val) (fibreList_terminal B.n j))
    let R := AddressOrder.mapSum additiveStructure A.val (totalPartitionOrder f)
    let r := rowsChart A.val (fibreList f) (List.finRange B.n)
    let x := act 𝒮 Z u.cell (List.finRange B.n)
    let z := R ≫ r ≫ x ≫ q
    have M (j : Fin 1) : (standardPushSplit f (terminalCarrier B.n) A.val j ≫
      (standardPushMap (terminalCarrier B.n) u.cell j ≫ (Q j ≫ q))) = P j ≫ z := by
      let a : fibreList (terminalCarrier B.n) j = List.finRange B.n := fibreList_terminal _ _
      let k := eqToHom (congrArg (fold 𝒮 Z (standardPushObj f A.val)) a)
      have s : standardPushMap (terminalCarrier B.n) u.cell j ≫ Q j = k ≫ x :=
        std_act_list_congr u.cell a
      have t : standardPushSplit f (terminalCarrier B.n) A.val j ≫ k = P j ≫ R ≫ r :=
        standardPush_terminal_chart f A.val j (totalPartitionOrder f)
      rw [← Category.assoc (standardPushMap _ _ _), s]
      simp only [Category.assoc]
      rw [reassoc_of% t]
    first
    |
      let _ : IsIso (P 0) := by unfold P; infer_instance
      have t := h (0 : Fin 1)
      change _ = 𝟙 _ ≫ (P 0 ≫ p) at t
      rw [Category.id_comp] at t
      exact (cancel_epi (P 0)).mp ((M 0).symm.trans t)
    |
      intro j
      change _ = 𝟙 _ ≫ (P j ≫ p)
      rw [Category.id_comp]
      exact (M j).trans (congrArg (fun t => P j ≫ t) h)

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
