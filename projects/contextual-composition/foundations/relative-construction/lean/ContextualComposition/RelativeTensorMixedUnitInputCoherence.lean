module
public import ContextualComposition.RelativeTensorMixedUnitOutputCoherence
public import ContextualComposition.RelativeTensorMixedInputComposition

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

universe v u
variable {B : Type u} [Category.{v} B]
variable (M N : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{v,v}))
variable (jM : unitModule B ⟶ M) (jN : unitModule B ⟶ N)

private abbrev unitInsertion (a d : B) :
    (column M d).obj ⟨op a⟩ ⥤ (column (middleComposite M N) d).obj ⟨op a⟩ :=
  CategoryTheory.Prod.sectL ((column M d).obj ⟨op a⟩) (nativeUnitValue jN (𝟙 d)) ⋙
    insertion (row M a) (column N d) d

private theorem mixedUnitInput_targetUnit {a d : B} (p : Discrete (a ⟶ d)) :
    (contravariantUnitAt (middleComposite M N) a d).app ((mixedUnitAt M N jM jN a d).obj p) =
      (unitInsertion M N jN a d).map
        ((contravariantUnitAt M a d).app (nativeUnitValue jM p.as)) := by
  rw [contravariantUnitAt_composite, tensorFirstUnit_app, First.cell_app]
  rfl

private theorem mixedUnitInput_targetComp {a b c : B} (d : B)
    (f : a ⟶ b) (g : b ⟶ c) (p : Discrete (c ⟶ d)) :
    (contravariantCompAt (middleComposite M N) d f g).app ((mixedUnitAt M N jM jN c d).obj p) =
      (unitInsertion M N jN a d).map
        ((contravariantCompAt M d f g).app (nativeUnitValue jM p.as)) := by
  rw [contravariantCompAt_composite, tensorFirstComp_app, First.cell_app]
  rfl

set_option maxHeartbeats 300000 in
/-- The original input comparison of the mixed unit preserves the actual
contravariant unitors of the pure hom module and retained tensor. -/
theorem mixedUnitInput_identity (a d : B) :
    RespectsEndpointIdentity (mixedUnitInput M N jM jN (b := d) (𝟙 a))
      (contravariantUnitAt (unitModule B) a d) (contravariantUnitAt (middleComposite M N) a d) := by
  intro p
  rw [mixedUnitInput_app, mixedUnitInput_targetUnit, mixedUnitAt_map]
  let J := unitInsertion M N jN a d
  change J.map _ ≫ J.map _ = J.map _
  rw [← J.map_comp]
  apply congrArg J.map
  have h := NatTrans.congr_app (congrArg Cat.Hom₂.toNatTrans ((jM.app ⟨d⟩).naturality_id ⟨op a⟩)) p
  change _ = _ ≫ 𝟙 _ ≫ 𝟙 _ at h
  simp only [Category.comp_id] at h
  exact h

set_option maxHeartbeats 400000 in
/-- The original input comparisons preserve the chosen contravariant
compositors. On the opposite boundary `g` acts before `f`. -/
theorem mixedUnitInput_composition {a b c : B} (d : B) (f : a ⟶ b) (g : b ⟶ c) :
    RespectsEndpointComposition (mixedUnitInput M N jM jN (b := d) g)
      (mixedUnitInput M N jM jN (b := d) f) (mixedUnitInput M N jM jN (b := d) (f ≫ g))
      (contravariantCompAt (unitModule B) d f g) (contravariantCompAt (middleComposite M N) d f g) := by
  intro p
  change (mixedUnitInput M N jM jN (b := d) (f ≫ g)).hom.app p ≫
      (contravariantCompAt (middleComposite M N) d f g).app ((mixedUnitAt M N jM jN c d).obj p) =
    (mixedUnitAt M N jM jN a d).map ((contravariantCompAt (unitModule B) d f g).app p) ≫
      (mixedUnitInput M N jM jN (b := d) f).hom.app ((backward (column (unitModule B) d) g).obj p) ≫
      (mapFirst (G := column N d) (Middle.change M f.op.toLoc)).map ((mixedUnitInput M N jM jN (b := d) g).hom.app p)
  rw [mixedUnitInput_app, mixedUnitInput_app, mixedUnitInput_app, mixedUnitInput_targetComp, mixedUnitAt_map,
    First.on_native]
  let J := unitInsertion M N jN a d
  change J.map _ ≫ J.map _ = J.map _ ≫ J.map _ ≫ J.map _
  simp only [← J.map_comp]
  apply congrArg J.map
  have h := NatTrans.congr_app (congrArg Cat.Hom₂.toNatTrans
    ((jM.app ⟨d⟩).naturality_comp g.op.toLoc f.op.toLoc)) p
  change _ = _ ≫ 𝟙 _ ≫ _ ≫ 𝟙 _ ≫ _ ≫ 𝟙 _ at h
  simp only [Category.id_comp, Category.comp_id] at h
  exact h


section CommonLevels
variable {C : Type u} [Category.{max u v} C]
variable (P Q : LocallyDiscrete C ⥤ᵖ (LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{max u v,max u v}))
variable (jP : unitModule C ⟶ P) (jQ : unitModule C ⟶ Q)
variable (d : C)

set_option maxHeartbeats 400000 in
/-- The original mixed unit bundled in the contravariant endpoint, with
output fixed and the native Cat levels shared. This proves no joint law. -/
def mixedUnitInputColumn : column (unitModule C) d ⟶ column (middleComposite P Q) d :=
  strongCatFromEndpointLaws
    (fun a => mixedUnitAt P Q jP jQ a.as.unop d)
    (fun f => mixedUnitInput P Q jP jQ f.as.unop)
    (fun a => mixedUnitInput_identity P Q jP jQ a.as.unop d)
    (fun f g => mixedUnitInput_composition P Q jP jQ d g.as.unop f.as.unop)

theorem mixedUnitInputColumn_app (a : C) :
    HEq ((mixedUnitInputColumn P Q jP jQ d).app ⟨op a⟩).toFunctor (mixedUnitAt P Q jP jQ a d) := by
  rfl

theorem mixedUnitInputColumn_naturality {a b : C} (f : a ⟶ b) :
    Cat.Hom.toNatIso ((mixedUnitInputColumn P Q jP jQ d).naturality f.op.toLoc) =
      mixedUnitInput P Q jP jQ (b := d) f := rfl
end CommonLevels
end ContextualComposition.RelativeTensor.Iterated
