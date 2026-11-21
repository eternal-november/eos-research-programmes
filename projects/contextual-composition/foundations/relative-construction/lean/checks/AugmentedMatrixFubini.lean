import ContextualComposition.AugmentedMatrixFubini
import Mathlib.Algebra.Field.Rat
import Mathlib.Tactic.NormNum

/-! Author-side positive and negative witnesses. -/

open scoped BigOperators
open ContextualComposition.AugmentedMatrixFubini

namespace Issue92Probes
noncomputable section

def outer : Family ℚ where
  Pos := Bool
  posFintype := inferInstance
  Basis _ := PUnit
  basisFintype _ := inferInstance
  epsilon _ _ := 1

def inner : Family ℚ where
  Pos := Bool
  posFintype := inferInstance
  Basis _ := Bool
  basisFintype _ := inferInstance
  epsilon _ xa := if xa.2 then 0 else 1

def innerTarget : Family ℚ where
  Pos := PUnit
  posFintype := inferInstance
  Basis _ := Bool
  basisFintype _ := inferInstance
  epsilon _ xa := if xa.2 then 0 else 1

def phaseEntry (branch b a : Bool) : ℚ :=
  if b = a then 1 else if branch && b && !a then 1 else 0

/-- A two-to-one carrier map, using identity or shear according to the
pre-merge outer branch. Both matrices preserve the first-coordinate row. -/
def phase (branch : Bool) : Hom inner innerTarget where
  pos _ := PUnit.unit
  block _ b a := phaseEntry branch b a
  aug x a := by
    change Bool at a
    change (∑ b : Bool, (if b then 0 else 1) * phaseEntry branch b a) = if a then 0 else 1
    cases a <;> cases branch <;> norm_num [Fintype.sum_bool, phaseEntry]

def branchMap : DepHom (fun _ : outer.Pos => inner) (fun _ : (unit ℚ).Pos => innerTarget) :=
  ⟨toUnit outer, phase⟩

def src : Bool → Family ℚ := fun _ => outer
def dst : Bool → Family ℚ := fun _ => unit ℚ
def srcQ : ∀ i, (src i).Pos → Family ℚ := fun _ _ => inner
def dstQ : ∀ i, (dst i).Pos → Family ℚ := fun _ _ => innerTarget

def arrows : ∀ i, DepHom (srcQ i) (dstQ i) := fun _ => branchMap

def firstOut : (rightFamily dst dstQ).Pos := ⟨fun _ => PUnit.unit, fun _ => PUnit.unit⟩
def taggedInput (branch : Bool) : (leftFamily src srcQ).Pos := fun i => ⟨branch && i, false⟩
def inColumn (branch : Bool) : (leftFamily src srcQ).Basis (taggedInput branch) :=
  fun _ => (PUnit.unit, false)

def outRow : (rightFamily dst dstQ).Basis firstOut :=
  (fun _ => PUnit.unit, fun i => i)

def route₁ := (fubiniLeftMap arrows).comp (fubini dst dstQ)
def route₂ := (fubini src srcQ).comp (fubiniRightMap arrows)

theorem routes_agree : route₁ = route₂ := fubini_natural arrows

/-- These are entries of the aggregated, not merely the unaggregated,
coefficient arrow at the one target carrier. -/
theorem shear_separates_native_columns :
    route₁.native firstOut outRow ⟨⟨taggedInput false, rfl⟩, inColumn false⟩ = 0 ∧
    route₂.native firstOut outRow ⟨⟨taggedInput true, rfl⟩, inColumn true⟩ = 1 := by
  rw [routes_agree]
  constructor
  · change mul (perm (fubiniBasis src srcQ (taggedInput false)))
      ((fubiniRightMap arrows).block (fubiniPos src srcQ (taggedInput false)))
      outRow (inColumn false) = 0
    refine (mul_perm_left _ _ _ _).trans ?_
    change (∏ _ : Bool, (1 : ℚ)) *
      (∏ i : Bool, phaseEntry (false && i) i false) = 0
    norm_num [Fintype.prod_bool, phaseEntry]
  · change mul (perm (fubiniBasis src srcQ (taggedInput true)))
      ((fubiniRightMap arrows).block (fubiniPos src srcQ (taggedInput true)))
      outRow (inColumn true) = 1
    refine (mul_perm_left _ _ _ _).trans ?_
    change (∏ _ : Bool, (1 : ℚ)) *
      (∏ i : Bool, phaseEntry (true && i) i false) = 1
    norm_num [Fintype.prod_bool, phaseEntry]

/-- The augmentation cannot detect the coefficient distinction. -/
theorem same_augmentation :
    (leftFamily src srcQ).weight (taggedInput false) (inColumn false) = 1 ∧
    (leftFamily src srcQ).weight (taggedInput true) (inColumn true) = 1 := by
  constructor <;> change (∏ _ : Bool, (1 : ℚ) * 1) = 1 <;> simp

/-- All early outer aggregation sees is a singleton carrier and the same
unit outer coefficient. The inner carrier also has a common raw address. -/
theorem equal_before_branch_sensitive_action :
    (fun i => branchMap.outer.pos ((taggedInput false i).1)) =
      (fun i => branchMap.outer.pos ((taggedInput true i).1)) ∧
    (fun i => branchMap.outer.block ((taggedInput false i).1) PUnit.unit PUnit.unit) =
      (fun i => branchMap.outer.block ((taggedInput true i).1) PUnit.unit PUnit.unit) ∧
    (fun i => (taggedInput false i).2) = (fun i => (taggedInput true i).2) :=
  ⟨rfl, rfl, rfl⟩

theorem merges_both_levels :
    ¬ Function.Injective branchMap.outer.pos ∧
    ¬ Function.Injective (branchMap.inner true).pos := by
  constructor <;> intro h <;> exact Bool.false_ne_true (h (a₁ := false) (a₂ := true) rfl)

/-- Distinct draws at two addresses of the very same family survive. -/
theorem repeated_occurrences_are_not_diagonal :
    ∃ x : (occurrence src).Pos, x false ≠ x true := ⟨fun i => i, Bool.false_ne_true⟩

def zeroWitness : Family ℚ where
  Pos := PUnit
  posFintype := inferInstance
  Basis _ := PUnit
  basisFintype _ := inferInstance
  epsilon _ _ := 0

def noWitness : Family ℚ where
  Pos := PEmpty
  posFintype := inferInstance
  Basis x := PEmpty.elim x
  basisFintype x := PEmpty.elim x
  epsilon _ p := PEmpty.elim p.1

theorem raw_zero_witness_retained :
    Nonempty zeroWitness.Pos ∧ (∀ x a, zeroWitness.weight x a = 0) ∧ IsEmpty noWitness.Pos :=
  ⟨⟨PUnit.unit⟩, fun _ _ => rfl, inferInstanceAs (IsEmpty PEmpty)⟩

def missed : Hom (unit ℚ) outer where
  pos _ := false
  block _ _ _ := 1
  aug _ _ := by change (∑ _ : PUnit, (1 : ℚ) * 1) = 1; simp

theorem empty_preimage_has_empty_native_domain :
    IsEmpty (Σ x : {x : (unit ℚ).Pos // missed.pos x = true}, (unit ℚ).Basis x.1) :=
  ⟨fun x => Bool.false_ne_true x.1.2⟩

theorem empty_continuation_is_not_unit :
    IsEmpty (dependent zeroWitness (fun _ => noWitness)).Pos :=
  ⟨fun xy => PEmpty.elim xy.2⟩

theorem empty_occurrence_has_unit_coefficient :
    ∃ x : (occurrence (fun _ : Empty => noWitness)).Pos,
      ∀ a, (occurrence (fun _ : Empty => noWitness)).weight x a = 1 := by
  refine ⟨fun i => i.elim, ?_⟩
  intro a
  change (∏ i : Empty, noWitness.weight (i.elim) (a i)) = 1
  simp

/-- In the matrix regime the empty preimage has exactly one *matrix*
with its specified output basis; it was not collapsed at carrier level. -/
theorem empty_native_block_unique
    (n : Matrix (outer.Basis true)
      (Σ x : {x : (unit ℚ).Pos // missed.pos x = true}, (unit ℚ).Basis x.1) ℚ) :
    missed.native true = n := by
  funext b a
  exact (empty_preimage_has_empty_native_domain.false a).elim

/-- The source-indexed shortcut is false in a general symmetric rig:
in finite sets opposite with sum and product on objects, an arrow from the
empty sum to Bool is a function Bool → Empty, with no inhabitants. A
component family indexed by an empty set would exist. -/
theorem opposite_finset_empty_obstruction :
    IsEmpty (Bool → Empty) ∧ Nonempty (Empty → (Bool → Empty)) :=
  ⟨⟨fun f => f false |>.elim⟩, ⟨fun x => x.elim⟩⟩

def eraseZero : Hom zeroWitness zeroWitness where
  pos x := x
  block _ _ _ := 0
  aug x a := by
    change (∑ _ : PUnit, (0 : ℚ) * 0) = 0
    simp

/-- A singleton with zero augmentation still carries distinguishable arrows. -/
theorem zero_augmentation_is_not_faithful : Hom.id zeroWitness ≠ eraseZero := by
  intro h
  have heq := congrArg
    (fun m : Hom zeroWitness zeroWitness => m.block PUnit.unit PUnit.unit PUnit.unit) h
  have h₁ : (Hom.id zeroWitness).block PUnit.unit PUnit.unit PUnit.unit = 1 := by
    change (perm (Equiv.refl PUnit) : Matrix PUnit PUnit ℚ) PUnit.unit PUnit.unit = 1
    simp [perm]
  have h₂ : eraseZero.block PUnit.unit PUnit.unit PUnit.unit = 0 := rfl
  rw [h₁, h₂] at heq
  exact one_ne_zero heq

end
end Issue92Probes
