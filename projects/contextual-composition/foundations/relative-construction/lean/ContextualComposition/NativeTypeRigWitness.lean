module
public import ContextualComposition.NativeSymmetricRigInterface
meta import Mathlib.Tactic.CasesM
@[expose] public section

/-! Concrete sets and functions: disjoint sum and cartesian
multiplication. All local rig laws are checked on actual functions. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.NativeTypeRig
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid DependentFubiniTree
open scoped MonoidalCategory

abbrev sets : Category.{0} (Type 0) where
  Hom A B := A → B
  id _ := id
  comp f g := g ∘ f

local instance : Category.{0} (Type 0) := sets

def ofEquiv {X Y : Type 0} (p : X ≃ Y) : X ≅ Y :=
  ⟨p.toFun, p.invFun, funext p.symm_apply_apply, funext p.apply_symm_apply⟩

abbrev plusStruct : MonoidalCategoryStruct (Type 0) where
  tensorObj := Sum
  tensorUnit := Empty
  tensorHom f g := Sum.map f g
  whiskerLeft _ {_ _} f := Sum.map id f
  whiskerRight {_ _} f _ := Sum.map f id
  associator _ _ _ := ofEquiv (Equiv.sumAssoc _ _ _)
  leftUnitor _ := ofEquiv (Equiv.emptySum _ _)
  rightUnitor _ := ofEquiv (Equiv.sumEmpty _ _)

local macro "set_sums" : tactic =>
  `(tactic| (intros; funext x; try dsimp (config := { zetaDelta := true }) only [plusStruct, MonoidalCategoryStruct.tensorObj, MonoidalCategoryStruct.tensorUnit] at x; cases x <;> (try casesm* Sum _ _, Empty) <;> rfl))

abbrev plusMonoidal : MonoidalCategory (Type 0) :=
  letI := plusStruct
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := by set_sums)
    (id_tensorHom := by set_sums)
    (tensorHom_id := by set_sums)
    (tensorHom_comp_tensorHom := by set_sums)
    (associator_naturality := by set_sums)
    (leftUnitor_naturality := by set_sums)
    (rightUnitor_naturality := by set_sums)
    (pentagon := by set_sums)
    (triangle := by set_sums)

abbrev plusSymmetric : @SymmetricCategory (Type 0) sets plusMonoidal :=
  letI := plusMonoidal
  { braiding := fun _ _ => ofEquiv (Equiv.sumComm _ _)
    braiding_naturality_right := by set_sums
    braiding_naturality_left := by set_sums
    hexagon_forward := by set_sums
    hexagon_reverse := by set_sums
    symmetry := by set_sums }

abbrev timesStruct : MonoidalCategoryStruct (Type 0) where
  tensorObj := Prod
  tensorUnit := Unit
  tensorHom f g := Prod.map f g
  whiskerLeft _ {_ _} f := Prod.map id f
  whiskerRight {_ _} f _ := Prod.map f id
  associator _ _ _ := ofEquiv (Equiv.prodAssoc _ _ _)
  leftUnitor _ := ofEquiv (Equiv.punitProd _)
  rightUnitor _ := ofEquiv (Equiv.prodPUnit _)

local macro "set_prods" : tactic =>
  `(tactic| (intros; first | rfl | (funext x; try dsimp at x ⊢; (try casesm* Prod _ _, Unit) <;> rfl)))

abbrev timesMonoidal : MonoidalCategory (Type 0) :=
  letI := timesStruct
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := by set_prods)
    (id_tensorHom := by set_prods)
    (tensorHom_id := by set_prods)
    (tensorHom_comp_tensorHom := by set_prods)
    (associator_naturality := by set_prods)
    (leftUnitor_naturality := by set_prods)
    (rightUnitor_naturality := by set_prods)
    (pentagon := by set_prods)
    (triangle := by set_prods)

abbrev timesSymmetric : @SymmetricCategory (Type 0) sets timesMonoidal :=
  letI := timesMonoidal
  { braiding := fun _ _ => ofEquiv (Equiv.prodComm _ _)
    braiding_naturality_right := by set_prods
    braiding_naturality_left := by set_prods
    hexagon_forward := by set_prods
    hexagon_reverse := by set_prods
    symmetry := by set_prods }

def tensorModel : TensorSemantics (Type 0) := ⟨timesMonoidal, timesSymmetric⟩

local instance : MonoidalCategory (Type 0) := plusMonoidal
local instance : SymmetricCategory (Type 0) := plusSymmetric

open Lean Meta Elab Tactic in
local elab "split_set_arguments" : tactic =>
  liftMetaTactic (fun goal => goal.casesMatching (fun t => do
    let t ← withTransparency .all (whnf t)
    pure (#[``Sum, ``Prod, ``Empty, ``Unit, ``PUnit].contains t.getAppFn.constName))
    (recursive := true) (allowSplit := true))

local macro "set_grid" : tactic =>
  `(tactic| (intros; funext x; (try split_set_arguments) <;> rfl))

def concreteGrid : NativeRigGrid tensorModel where
  leftSplit a :=
    { nil := ofEquiv (Equiv.prodEmpty a)
      bin := fun b c => ofEquiv (Equiv.prodSumDistrib a b c) }
  rightDist a b :=
    NatIso.ofComponents (fun c => ofEquiv (Equiv.sumProdDistrib a b c)) (by set_grid)
  absorbLeft :=
    NatIso.ofComponents (fun c => ofEquiv (Equiv.emptyProd c)) (by set_grid)
  rightDist_preserves _ _ :=
    { bin := by set_grid
      nil := by set_grid }
  absorbLeft_preserves :=
    { bin := by set_grid
      nil := by set_grid }

theorem concreteLocalLaws : NativeRigLocalLaws tensorModel concreteGrid where
  natural :=
    { left := by set_grid
      right := by set_grid
      absorbRight := by set_grid }
  leftContext _ :=
    { natural := ⟨by set_grid⟩
      assoc := ⟨by set_grid⟩
      swap := ⟨by set_grid⟩
      left := by set_grid
      right := by set_grid }
  rightContext _ :=
    { natural := ⟨by set_grid⟩
      assoc := ⟨by set_grid⟩
      swap := ⟨by set_grid⟩
      left := by set_grid
      right := by set_grid }
  primitive :=
    { ar := fun _ _ => ⟨by set_grid, by set_grid⟩
      am := fun _ _ => ⟨by set_grid, by set_grid⟩
      al := fun _ _ => ⟨by set_grid, by set_grid⟩
      sr := fun _ => ⟨by set_grid, by set_grid⟩
      sl := fun _ => ⟨by set_grid, by set_grid⟩ }
  rightUnit_zero := by set_grid
  rightUnit_bin := by set_grid

def concreteRig : CoherentNativeRig tensorModel := ⟨concreteGrid, concreteLocalLaws⟩

section ConcreteNative
open IndexedNativeFamily
local notation "ℙ" => standardPush (C:=(Type 0))

def allDisplays : NativeProjectionClass.{1} where
  admissible _ := True
  ident _ := trivial
  equiv _ := trivial
  comp _ _ := trivial
  pullback _ _ _ := trivial

/-- Two retained addresses tagged separately even though both carry Bool. -/
noncomputable def two : Aug ℙ Unit where
  base := ⟨2,fun _ => Bool⟩
  ε := ⟨fun _ => (0 : Fin 1), fun _ _ => ()⟩

/-- The native carrier identifies the two sources, and its other fibre is
empty. The selected Boolean is the actual value of its whole-fibre map. -/
noncomputable def merge (b : Bool) : AugHom ℙ two two where
  native := ⟨fun _ => (0 : Fin 2), fun _ _ => b⟩
  preserves := by
    apply native_hom_eq_of_cell_heq
    · rfl
    · intro j
      apply heq_of_eq
      exact funext fun _ => @Subsingleton.elim Unit inferInstance _ _

theorem merge_carrier (b : Bool) : (merge b).native.addr (0 : Fin 2) = (merge b).native.addr (1 : Fin 2) := rfl

/-- The empty preimage is a real nullary coefficient domain. -/
theorem merge_empty_fibre (b : Bool) :
    (ℙ).obj (merge b).native.addr two.base.val (1 : Fin 2) = Empty := rfl

set_option backward.isDefEq.respectTransparency false in
theorem merge_cell_distinct : merge false ≠ merge true := by
  intro h
  have hn := congrArg AugHom.native h
  have hc := eq_of_heq (Hom.mk.inj hn).2
  have hv := congrFun hc (0 : Fin 2)
  let x : (ℙ).obj (fun _ : Fin 2 => (0 : Fin 2)) (fun _ => Bool) 0 := Sum.inl false
  have he := congrFun hv x
  exact Bool.noConfusion he

noncomputable def input : AdmissibleDependentInput (C:=Type 0) allDisplays PUnit.{2} Unit where
  parent := ⟨fun _ => two, trivial⟩
  child := ⟨fun _ => two, trivial⟩

noncomputable def inputMerge (b c : Bool) : AdmissibleDependentArrow input input where
  parent := ObjectProperty.homMk (fun _ => merge b)
  child := fun _ => merge c

/-- The two independently constructed routes on actual many-to-one
parent and continuation arrows in the common source-facing interface. -/
theorem concrete_fubini_square (b c : Bool) :
    concreteRig.separateMap tensorModel allDisplays 2 (fun _ => inputMerge b c) ≫
      (concreteRig.fubini tensorModel allDisplays 2 (fun _ => input)).hom =
    (concreteRig.fubini tensorModel allDisplays 2 (fun _ => input)).hom ≫
      concreteRig.jointMap tensorModel allDisplays 2 (fun _ => inputMerge b c) :=
  concreteRig.fubini_natural tensorModel allDisplays 2 (fun _ => inputMerge b c)

/-- The two occurrences are genuine, not one factor on a diagonal:
each input has four branches and their tensor has sixteen. -/
theorem concrete_fubini_address_count :
    ((nativeFubiniSeparate (concreteRig.rightGather tensorModel) (concreteRig.leftGathering tensorModel)
      (concreteRig.unit tensorModel) allDisplays 2 (fun _ => input)).obj PUnit.unit).base.n = 16 := by
  rfl

theorem concrete_fubini_joint_address_count :
    ((nativeFubiniJoint (concreteRig.rightGather tensorModel) (concreteRig.leftGathering tensorModel)
      (concreteRig.unit tensorModel) allDisplays 2 (fun _ => input)).obj PUnit.unit).base.n = 16 := rfl

/-- No quotient of the carrier by zero coefficient: an Empty-labelled
address survives as a genuine occurrence in the original native family. -/
noncomputable def zeroLabelFamily : Aug ℙ Unit where
  base := ⟨1, fun _ => Empty⟩
  ε := ⟨fun _ => (0 : Fin 1), fun _ _ => ()⟩

noncomputable def noAddresses : Aug ℙ Unit where
  base := ⟨0, Fin.elim0⟩
  ε := ⟨Fin.elim0, fun _ _ => ()⟩

theorem zero_label_retained : zeroLabelFamily ≠ noAddresses := by
  intro h
  exact Nat.noConfusion (congrArg (fun A : Aug ℙ Unit => A.base.n) h)

theorem unit_not_no_addresses : AugHom.unit (S:=ℙ) Unit ≠ noAddresses := by
  intro h
  exact Nat.noConfusion (congrArg (fun A : Aug ℙ Unit => A.base.n) h)

end ConcreteNative

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.NativeTypeRig
