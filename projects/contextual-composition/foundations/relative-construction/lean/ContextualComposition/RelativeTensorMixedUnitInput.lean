module
public import ContextualComposition.RelativeTensorMixedOperations

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
universe v u
variable {B : Type u} [Category.{v} B]
variable (M N : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{v,v}))
variable (jM : unitModule B ⟶ M) (jN : unitModule B ⟶ N)
variable {a' a b : B} (u : a' ⟶ a)

/-- Input reindexing of the actual mixed unit uses the supplied first unit's naturality isomorphism at the pure label. -/
def mixedUnitInput :
    backward (column (unitModule B) b) u ⋙ mixedUnitAt M N jM jN a' b ≅
      mixedUnitAt M N jM jN a b ⋙ backward (column (middleComposite M N) b) u :=
  Discrete.natIso fun p =>
    (insertion (row M a') (column N b) b).mapIso
      (((Cat.Hom.toNatIso ((jM.app ⟨b⟩).naturality u.op.toLoc)).app p).prod
        (Iso.refl (((jN.app ⟨b⟩).app ⟨op b⟩).toFunctor.obj (Discrete.mk (𝟙 b)))))

theorem mixedUnitInput_app (p : Discrete (a ⟶ b)) :
    (mixedUnitInput M N jM jN u).hom.app p =
      (insertion (row M a') (column N b) b).map (productMap
        (((jM.app ⟨b⟩).naturality u.op.toLoc).hom.toNatTrans.app p)
        (𝟙 (((jN.app ⟨b⟩).app ⟨op b⟩).toFunctor.obj (Discrete.mk (𝟙 b))))) := rfl

end ContextualComposition.RelativeTensor.Iterated
