module
public import ContextualComposition.RelativeTensorMixedUnitInput

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
variable {a b c : B}

abbrev nativeUnitValue
    {P : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{v,v})}
    (j : unitModule B ⟶ P) {i k : B} (p : i ⟶ k) : (column P k).obj ⟨op i⟩ :=
  ((j.app ⟨k⟩).app ⟨op i⟩).toFunctor.obj (Discrete.mk p)

/-- The first supplied unit carries postcomposition of a pure label to the
chosen covariant transition of the first weak module. -/
def mixedUnitOutputFirst (g : b ⟶ c) (p : a ⟶ b) :
    nativeUnitValue jM (p ≫ g) ≅ (forward (row M a) g).obj (nativeUnitValue jM p) :=
  (Cat.Hom.toNatIso ((Middle.evaluate (⟨op a⟩ : LocallyDiscrete Bᵒᵖ)).map₂Iso
    (jM.naturality g.toLoc))).app (Discrete.mk p)

/-- Compare the two routes for the second supplied unit on the pure arrow
`g`: use its chosen input square backwards and its chosen output square forwards. -/
def mixedUnitOutputSecond (g : b ⟶ c) :
    (backward (column N c) g).obj (nativeUnitValue jN (𝟙 c)) ≅
      (Second.part (N.map g.toLoc) b).obj (nativeUnitValue jN (𝟙 b)) :=
  ((Cat.Hom.toNatIso ((jN.app ⟨c⟩).naturality g.op.toLoc)).app (Discrete.mk (𝟙 c))).symm ≪≫
    eqToIso (congrArg (fun p : b ⟶ c => nativeUnitValue jN p)
      ((Category.comp_id g).trans (Category.id_comp g).symm)) ≪≫
    (Cat.Hom.toNatIso ((Middle.evaluate (⟨op b⟩ : LocallyDiscrete Bᵒᵖ)).map₂Iso
      (jN.naturality g.toLoc))).app (Discrete.mk (𝟙 b))

/-- Output change for the actual mixed unit on the retained tensor. The
comparison moves the postcomposed unit pair across the inverse middle balance. -/
def mixedUnitOutput (g : b ⟶ c) :
    forward (row (unitModule B) a) g ⋙ mixedUnitAt M N jM jN a c ≅
      mixedUnitAt M N jM jN a b ⋙
        (((middleComposite M N).map g.toLoc).app ⟨op a⟩).toFunctor :=
  Discrete.natIso fun p =>
    (insertion (row M a) (column N c) c).mapIso
      ((mixedUnitOutputFirst M jM g p.as).prod (Iso.refl (nativeUnitValue jN (𝟙 c)))) ≪≫
    (balancing (row M a) (column N c) g (nativeUnitValue jM p.as) (nativeUnitValue jN (𝟙 c))).symm ≪≫
    (insertion (row M a) (column N c) b).mapIso
      ((Iso.refl (nativeUnitValue jM p.as)).prod (mixedUnitOutputSecond N jN g))

/-- The actual output comparison retains the two supplied unit cells and the
inverse balance at the indicated labels; it is not an identity transport. -/
theorem mixedUnitOutput_app (g : b ⟶ c) (p : Discrete (a ⟶ b)) :
    (mixedUnitOutput M N jM jN g).hom.app p =
      (insertion (row M a) (column N c) c).map
        (productMap (mixedUnitOutputFirst M jM g p.as).hom (𝟙 (nativeUnitValue jN (𝟙 c)))) ≫
      (balancing (row M a) (column N c) g (nativeUnitValue jM p.as) (nativeUnitValue jN (𝟙 c))).inv ≫
      (insertion (row M a) (column N c) b).map
        (productMap (𝟙 (nativeUnitValue jM p.as)) (mixedUnitOutputSecond N jN g).hom) := rfl

end ContextualComposition.RelativeTensor.Iterated
