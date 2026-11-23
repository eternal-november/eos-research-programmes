import ContextualComposition.NativeWordMap
import Mathlib.CategoryTheory.Types.Basic

/-! A two-tag boundary: the source labels are both Bool, both source tags
map to false, and the target tag true has an empty fibre with a genuine
independent cell. Both the source and target lists are reversed. -/
namespace NativeWordOrderFixture
open CategoryTheory MonoidalCategory
open ContextualComposition.NativeFinitePush
open ContextualComposition.NativeFinitePush.DependentFibre
open ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open ContextualComposition.RigGrid
open scoped CategoryTheory MonoidalCategory

-- Use products on types so that swapping two equal coefficients is visible
-- and the unit PUnit still admits distinct maps to Bool. Keep the instance
-- local: this is a probe, not a new global choice of monoidal structure.
local instance : MonoidalCategory (Type 0) where
  tensorObj := Prod
  whiskerLeft _ {_ _} f := ↾fun x => (x.1, f x.2)
  whiskerRight f _ := ↾fun x => (f x.1, x.2)
  tensorUnit := PUnit
  associator X Y Z := (Equiv.prodAssoc X Y Z).toIso
  leftUnitor X := (Equiv.punitProd X).toIso
  rightUnitor X := (Equiv.prodPUnit X).toIso
  tensorHom_def _ _ := rfl
  id_tensorHom_id _ _ := rfl
  tensorHom_comp_tensorHom _ _ _ _ := rfl
  whiskerLeft_id _ _ := rfl
  id_whiskerRight _ _ := rfl
  associator_naturality _ _ _ := rfl
  leftUnitor_naturality _ := rfl
  rightUnitor_naturality _ := rfl
  pentagon _ _ _ _ := rfl
  triangle _ _ := rfl

local instance : SymmetricCategory (Type 0) where
  braiding X Y := (Equiv.prodComm X Y).toIso
  braiding_naturality_right := by intros; rfl
  braiding_naturality_left _ _ := rfl
  hexagon_forward _ _ _ := rfl
  hexagon_reverse _ _ _ := rfl
  symmetry _ _ := rfl

local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=Type 0)))
local notation "𝔉" => fold 𝒮 (𝟙_ (Type 0))
local notation "ℙ" => standardPush (C:=Type 0)
private def labels : Bool → Type := fun _ => Bool
private def merge : Bool → Bool := fun _ => false
private abbrev original : List Bool := [false, true]
private abbrev reversed : List Bool := [true, false]
private def swapTags : AddressOrder Bool original reversed := .swap false true []
private theorem distinct : original.Nodup := by decide
private theorem support : ∀ x ∈ original, merge x ∈ original := by decide

private def cell (b : Bool) (y : Bool) (_ : y ∈ original) :
    𝔉 labels (wordFibre original merge y) ⟶ labels y := by
  cases y
  · change Bool × (Bool × PUnit) ⟶ Bool
    exact ↾fun a => a.1
  · change PUnit ⟶ Bool
    exact ↾fun _ => b

private noncomputable def moved (b : Bool) :
    ∀ y ∈ reversed, 𝔉 labels (wordFibre reversed merge y) ⟶ labels y :=
  wordNativeMap_reorderCell labels labels swapTags swapTags distinct (cell b)

private noncomputable def old (b : Bool) : Hom ℙ (wordFamily labels original) (wordFamily labels original) :=
  wordNativeMap merge support distinct labels labels (fun j => cell b original[j] (List.getElem_mem _))

private noncomputable def new (b : Bool) : Hom ℙ (wordFamily labels reversed) (wordFamily labels reversed) :=
  wordNativeMap merge (wordReorder_support swapTags swapTags support) (swapTags.perm.nodup distinct)
    labels labels (fun j => moved b reversed[j] (List.getElem_mem _))

theorem test_square (b : Bool) :
    (old b).comp (wordReorderIso labels swapTags distinct).hom =
      (wordReorderIso labels swapTags distinct).hom.comp (new b) :=
  wordNativeMap_reorder labels labels swapTags swapTags distinct distinct support (cell b)

theorem shape :
    labels false = labels true ∧ false ≠ true ∧ merge false = merge true ∧
    wordFibre original merge false = original ∧
    wordFibre reversed merge false = reversed ∧ wordFibre reversed merge true = [] := ⟨rfl, by decide⟩

theorem repeats_do_not_erase_swap (b : Bool) :
    TypeCat.homEquiv (moved b false (by decide)) (false, (true, PUnit.unit)) = true := by
  let e := wordFibreOrderIso (f:=merge) labels swapTags distinct false
  let r := wordFibreOrder merge swapTags false
  let s := Classical.choice (AddressOrder.ofPerm r.perm.symm)
  have h : e.inv = AddressOrder.mapSum additiveStructure labels (.swap true false []) := by
    change AddressOrder.mapSum additiveStructure labels s = _
    exact tagged_permutation_coherent labels (by decide) s (.swap true false [])
  change TypeCat.homEquiv (e.inv ≫ cell b false _) (false, (true, PUnit.unit)) = true
  rw [h]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem empty_native_cells_remain_distinct : new false ≠ new true := by
  intro h
  have e := (native_hom_iff_cell rfl _ _).1 h (0 : Fin reversed.length)
  rw [eqToHom_refl, Category.id_comp] at e
  have e' := (cancel_epi (eqToHom (wordCarrier_fibre_pin merge
    (wordReorder_support swapTags swapTags support) (swapTags.perm.nodup distinct) labels (0 : Fin reversed.length)))).mp e
  change moved false true _ = moved true true _ at e'
  have h' := (wordNativeMap_reorderCell_eq_iff labels labels swapTags swapTags distinct
    (cell false) (cell true) true (by decide)).mp e'
  exact Bool.noConfusion (congrArg (fun p => TypeCat.homEquiv p PUnit.unit) h')

end NativeWordOrderFixture

open ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
#check wordFibreOrderIso
#check wordReorderIso
#check wordReorder_support
#check wordNativeMap_reorderCell
#check wordNativeMap_reorderCell_eq_iff
#check wordNativeMap_reorder
#print axioms wordFibreOrderIso
#print axioms wordReorderIso
#print axioms wordReorder_support
#print axioms wordNativeMap_reorderCell
#print axioms wordNativeMap_reorderCell_eq_iff
#print axioms wordNativeMap_reorder
#print axioms NativeWordOrderFixture.test_square
#print axioms NativeWordOrderFixture.shape
#print axioms NativeWordOrderFixture.repeats_do_not_erase_swap
#print axioms NativeWordOrderFixture.empty_native_cells_remain_distinct
