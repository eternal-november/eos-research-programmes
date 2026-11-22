module
public import ContextualComposition.StructuralLinearity
public import ContextualComposition.RigGridNativeAdapter
@[expose] public section
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory BraidedCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
set_option backward.isDefEq.respectTransparency false
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
abbrev tensorPrimitives : TensorPrimitive (binary (Binary.ofMonoidal (C:=C))) where
  assoc a b c := (α_ a b c).hom
  unassoc a b c := (α_ a b c).inv
  swap a b := (β_ a b).hom
  assoc_nat := associator_naturality
  unassoc_nat := associator_inv_naturality
  swap_nat := braiding_naturality
theorem middle_formula (a b c d : C) :
    (additiveMiddle (Additive.ofBraided (C:=C))).cell a b c d =
      zigMiddle (tensorPrimitives (C:=C)) a b c d := by
  change tensorμ a b c d = _
  unfold tensorμ zigMiddle
  simp only [coeff, binary, Binary.ofMonoidal, id_tensorHom, tensorHom_id]
variable {S : Bi (coeff (C:=C))} {Z : C}
variable (R : Gather S (binary (Binary.ofMonoidal (C:=C))) Z)
    (L : LeftGather S (binary (Binary.ofMonoidal (C:=C))) Z)
theorem braided_middle_linear (h : ForwardPrimitive R L (tensorPrimitives (C:=C)))
    (nr : GatherOuterNat R) (nl : GatherLeftNat L) :
    MedialLinear (additiveMiddle (Additive.ofBraided (C:=C))) R L ∧
      MedialInner (additiveMiddle (Additive.ofBraided (C:=C))) R L := by
  have q := ForwardPrimitive.upgrade R L _ h (fun a b c => (α_ a b c).hom_inv_id) (fun a b c => (α_ a b c).inv_hom_id)
  exact all_middle_linearity R L _ q nr nl _ middle_formula

section Grid
variable {D : Additive (C:=C)} (grid : GridData D) (n : GridNatural grid)
include n in
omit [MonoidalCategory C] [BraidedCategory C] in
theorem leftGatherNatural : GatherLeftNat (leftGather grid) where
  inner a := ⟨fun {x b _ d} p q => by
    change D.sum.map (grid.mul.map (𝟙 a) p) (grid.mul.map (𝟙 a) q) ≫
      ((grid.leftSplit a).bin _ d).inv =
      ((grid.leftSplit a).bin _ b).inv ≫ grid.mul.map (𝟙 a) (D.sum.map p q)
    apply (Iso.comp_inv_eq _).2
    let i := (grid.leftSplit a).bin x b
    simpa only [Category.assoc] using
      (i.inv_hom_id_assoc _).symm.trans (congrArg (fun m => i.inv ≫ m) (n.left (𝟙 a) p q).symm)⟩
  outer {a b} p := by
    constructor
    · change (grid.leftSplit a).nil.inv ≫ grid.mul.map p (𝟙 D.zero) = (grid.leftSplit b).nil.inv
      apply (cancel_mono (grid.leftSplit b).nil.hom).mp
      rw [Category.assoc, n.absorbRight p, Iso.inv_hom_id, Iso.inv_hom_id]
    · intro x y
      change ((grid.leftSplit a).bin x y).inv ≫ grid.mul.map p (𝟙 (D.sum.obj x y)) =
        D.sum.map (grid.mul.map p (𝟙 x)) (grid.mul.map p (𝟙 y)) ≫ ((grid.leftSplit b).bin x y).inv
      rw [← D.sum.map_id]
      symm
      apply (Iso.comp_inv_eq _).2
      let i := (grid.leftSplit a).bin x y
      simpa only [Category.assoc] using
        (i.inv_hom_id_assoc _).symm.trans (congrArg (fun m => i.inv ≫ m) (n.left p (𝟙 x) (𝟙 y)).symm)
end Grid
end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
