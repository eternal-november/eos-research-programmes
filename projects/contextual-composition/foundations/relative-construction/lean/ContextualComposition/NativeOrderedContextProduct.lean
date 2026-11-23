module
public import ContextualComposition.NativeOrderedContext
@[expose] public section

/-! Independent product of presented context inputs preserves display
admissibility, using pointwise products and reindexing of continuations. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.IndexedNativeFamily
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable {T : Bi (coeff (C:=C))} {I : C}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (J : UnitCompat R I)
variable {A : Type u}
variable (D E : A → OrderedDependentAugData I)
set_option quotPrecheck false in
local notation "prd" => fun x : A => (D x).product R L J (E x)

set_option backward.isDefEq.respectTransparency false in
theorem orderedParent_product :
    orderedParent (prd) = tensor R L J (orderedParent D) (orderedParent E) := by
  funext x
  exact (independentAug_ordered_eq R L (J.ρ I) (D x).V (E x).V (D x).xs (E x).xs (D x).ε (E x).ε).symm

set_option backward.isDefEq.respectTransparency false in
noncomputable def orderedProductLeft : (orderedParent (prd)).Extension → (orderedParent D).Extension :=
  fun z =>
    let w := ((prd) z.1).xs[z.2.down]
    let h := (dependentWord_mem (D z.1).xs (fun _ => (E z.1).xs) w).mp (List.getElem_mem _)
    ⟨z.1,⟨(wordPositions (D z.1).xs (D z.1).xs_unique).symm ⟨w.1,h.1⟩⟩⟩

set_option backward.isDefEq.respectTransparency false in
noncomputable def orderedProductRight : (orderedParent (prd)).Extension → (orderedParent E).Extension :=
  fun z =>
    let w := ((prd) z.1).xs[z.2.down]
    let h := (dependentWord_mem (D z.1).xs (fun _ => (E z.1).xs) w).mp (List.getElem_mem _)
    ⟨z.1,⟨(wordPositions (E z.1).xs (E z.1).xs_unique).symm ⟨w.2,h.2⟩⟩⟩

set_option backward.isDefEq.respectTransparency false in
theorem orderedProductLeft_read (z : (orderedParent (prd)).Extension) :
    (D z.1).xs[(orderedProductLeft R L J D E z).2.down] = (((prd) z.1).xs[z.2.down]).1 :=
  congrArg Subtype.val ((wordPositions (D z.1).xs (D z.1).xs_unique).apply_symm_apply _)

set_option backward.isDefEq.respectTransparency false in
theorem orderedProductRight_read (z : (orderedParent (prd)).Extension) :
    (E z.1).xs[(orderedProductRight R L J D E z).2.down] = (((prd) z.1).xs[z.2.down]).2 :=
  congrArg Subtype.val ((wordPositions (E z.1).xs (E z.1).xs_unique).apply_symm_apply _)

set_option backward.isDefEq.respectTransparency false in
theorem orderedChildren_product :
    orderedChildren (prd) = tensor R L J
      ((orderedChildren D).reindex (orderedProductLeft R L J D E))
      ((orderedChildren E).reindex (orderedProductRight R L J D E)) := by
  funext z
  let u := D z.1
  let v := E z.1
  let w := ((prd) z.1).xs[z.2.down]
  change ((prd) z.1).childAug w = independentAug R L (J.ρ I)
    (u.childAug (D z.1).xs[(orderedProductLeft R L J D E z).2.down])
    (v.childAug (E z.1).xs[(orderedProductRight R L J D E z).2.down])
  rw [orderedProductLeft_read, orderedProductRight_read]
  exact (independentAug_ordered_eq R L (J.ρ I) (u.A w.1) (v.A w.2) (u.us w.1) (v.us w.2)
    (u.δ w.1) (v.δ w.2)).symm

variable (K : NativeProjectionClass.{u})

theorem orderedProduct_admissible
    (d : OrderedAdmissible D K) (e : OrderedAdmissible E K) : OrderedAdmissible (prd) K := by
  constructor
  · rw [orderedParent_product]
    exact tensor_admissible K R L J _ _ d.parent e.parent
  · rw [orderedChildren_product]
    exact tensor_admissible K R L J _ _
      (reindex_admissible K _ d.children (orderedProductLeft R L J D E))
      (reindex_admissible K _ e.children (orderedProductRight R L J D E))

theorem orderedUnit_admissible :
    OrderedAdmissible (C:=C) (I:=I) (fun _ : A => OrderedDependentAugData.unit I) K := by
  constructor
  · have h : orderedParent (fun _ : A => OrderedDependentAugData.unit I) = constantUnit := by
      funext _
      exact unit_wordAug.symm
    rw [h]
    exact unit_admissible K
  · have h : orderedChildren (fun _ : A => OrderedDependentAugData.unit I) = constantUnit := by
      funext _
      exact unit_wordAug.symm
    rw [h]
    exact unit_admissible K

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.IndexedNativeFamily
