module

public import ContextualComposition.RigGridMonoidal
public import ContextualComposition.RaggedFubini

@[expose] public section

/-! Bridges only the datum actually supplied by the repository's distributor grid.
The tensor-middle linearity and unitor/distributor compatibility are separate obligations. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter

open CategoryTheory MonoidalCategory BraidedCategory ContextualComposition.RigGrid
open scoped MonoidalCategory

set_option backward.isDefEq.respectTransparency false

universe u v
variable {C : Type u} [Category.{v} C]

abbrev coeff : Coeff.{u,v} C where
  Hom a b := a ⟶ b
  id := CategoryStruct.id
  seq := CategoryStruct.comp
  id_seq := Category.id_comp
  seq_id := Category.comp_id
  assoc := Category.assoc

abbrev binary (F : Binary (C := C)) : Bi (coeff (C := C)) where
  obj := F.obj
  map := F.map
  map_id := F.map_id
  map_seq := F.map_comp

variable {S : Additive (C := C)} (K : GridData S)

abbrev gather : Gather (binary S.sum) (binary K.mul) S.zero where
  nil c := (K.absorbLeft.app c).inv
  cons a b c := ((K.rightDist a b).app c).inv
  nil_nat q := by
    let h := K.absorbLeft.inv.naturality q
    change (𝟙 S.zero) ≫ (K.absorbLeft.app _).inv =
      (K.absorbLeft.app _).inv ≫ K.mul.map (𝟙 S.zero) q at h
    exact h.symm.trans (Category.id_comp _)
  cons_nat a b {_ _} q := ((K.rightDist a b).inv.naturality q).symm

abbrev leftGather : LeftGather (binary S.sum) (binary K.mul) S.zero where
  nil a := (K.leftSplit a).nil.inv
  cons a b d := ((K.leftSplit a).bin b d).inv

def rightGatherIso (a b c : C) : Inv ((gather K).cons a b c) :=
  let i := (K.rightDist a b).app c
  ⟨i.hom, i.inv_hom_id, i.hom_inv_id⟩

def rightAbsorptionIso (c : C) : Inv ((gather K).nil c) :=
  let i := K.absorbLeft.app c
  ⟨i.hom, i.inv_hom_id, i.hom_inv_id⟩

def leftGatherIso (a b d : C) : Inv ((leftGather K).cons a b d) :=
  let i := (K.leftSplit a).bin b d
  ⟨i.hom, i.inv_hom_id, i.hom_inv_id⟩

def leftAbsorptionIso (a : C) : Inv ((leftGather K).nil a) :=
  let i := (K.leftSplit a).nil
  ⟨i.hom, i.inv_hom_id, i.hom_inv_id⟩

theorem gatherOuter (N : GridNatural K) : GatherOuterNat (gather K) where
  cons {a a' b b'} p q c := by
    change S.sum.map (K.mul.map p (𝟙 c)) (K.mul.map q (𝟙 c)) ≫ ((K.rightDist _ _).app c).inv =
      ((K.rightDist _ _).app c).inv ≫ K.mul.map (S.sum.map p q) (𝟙 c)
    apply (Iso.comp_inv_eq _).2
    let i := (K.rightDist a b).app c
    let h := N.right p q (𝟙 c)
    simpa only [Category.assoc] using (i.inv_hom_id_assoc _).symm.trans (congrArg (fun m => i.inv ≫ m) h.symm)

abbrev additiveMiddle (S : Additive (C := C)) : Middle (binary S.sum) S.zero where
  empty := S.mergeZero.inv
  cell a b c d := (S.middle a b c d).hom
  nat := S.middle_natural

abbrev additiveMiddleInv (S : Additive (C := C)) : MiddleInv (additiveMiddle S) where
  empty := ⟨S.mergeZero.hom,S.mergeZero.inv_hom_id,S.mergeZero.hom_inv_id⟩
  cell a b c d := ⟨(S.middle a b c d).inv,(S.middle a b c d).hom_inv_id,(S.middle a b c d).inv_hom_id⟩

abbrev additiveStructure [MonoidalCategory C] [BraidedCategory C] :
    AddStruct (binary (Additive.ofBraided (C := C)).sum) (𝟙_ C) where
  unitInv a := (λ_ a).inv
  assoc a b c := (α_ a b c).hom
  assocInv a b c := (α_ a b c).inv
  swap a b := (β_ a b).hom

theorem additiveNaturality [MonoidalCategory C] [BraidedCategory C] :
    AddNat (additiveStructure (C := C)) where
  unit p := by
    simpa only [additiveStructure, binary, Additive.ofBraided, Binary.ofMonoidal, coeff, id_tensorHom]
      using leftUnitor_inv_naturality p
  assoc := associator_naturality
  inv := associator_inv_naturality
  swap := braiding_naturality

/-- The available multiplicative monoidal instance supplies the actual right
unitor and its ordinary naturality. The binary/zero equations with gathering
remain premises, rather than being silently assumed of `GridData`. -/
def multiplicativeUnit [MonoidalCategory C] {A : Bi (coeff (C := C))} {Z : C}
    (G : Gather A (binary (Binary.ofMonoidal (C := C))) Z)
    (nil : G.nil (𝟙_ C) ≫ (ρ_ Z).hom = 𝟙 Z)
    (cons : ∀ a b, G.cons a b (𝟙_ C) ≫ (ρ_ (A.obj a b)).hom =
      A.map (ρ_ a).hom (ρ_ b).hom) : UnitCompat G (𝟙_ C) where
  ρ a := (ρ_ a).hom
  natural p := by
    simpa only [binary, Binary.ofMonoidal, coeff, tensorHom_id] using rightUnitor_naturality p
  nil := nil
  cons := cons

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
