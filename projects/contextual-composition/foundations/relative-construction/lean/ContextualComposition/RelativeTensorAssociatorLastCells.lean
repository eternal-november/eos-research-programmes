module
public import ContextualComposition.RelativeTensorAssociatorLastChange

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
universe vB uB vC uC vD uD vX uX vM uM vY uY
variable {B : Type uB} {C : Type uC} [Category.{vB} B] [Category.{vC} C]
variable (X : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX})
variable (M : LocallyDiscrete C ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM}))
variable {Y Y' : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vY,uY}}

def lastMapCell {s t : Y ⟶ Y'} (m : s ⟶ t) : lastMap M s ⟶ lastMap M t :=
  Factorization.Endpoint.Indexed.reindexCell (Middle.transpose M) (Parametric.varyCell m)

/-- Rebracketing carries the entire directed last-factor modification to its induced nested component. -/
theorem last_cell_app {s t : Y ⟶ Y'} (m : s ⟶ t) (z : Left X M Y) :
    (associate X M Y').map ((Second.mapCell (F := leftInner X M) m.as).app z) =
      (Second.mapCell (F := X) (lastMapCell M m).as).app ((associate X M Y).obj z) := by
  obtain ⟨⟨c,⟨⟨b,x,k⟩⟩,y⟩⟩ := z
  let z := (insertion X (column M c) b).obj (x,k)
  let g := (m.as.app ⟨op c⟩).toNatTrans.app y
  change (associate X M Y').map ((Reverse.insertL X M Y' c).map (productMap (𝟙 z) g)) =
    (keep X M Y' x).map ((insertM M Y' b c).map (productMap (𝟙 k) g))
  rw [associate_native,outer_leaf]

theorem last_modification {s t : Y ⟶ Y'} (m : s ⟶ t) :
    Functor.whiskerRight (Second.mapCell (F := leftInner X M) m.as) (associate X M Y') ≫ eqToHom (last_naturality X M t) =
      eqToHom (last_naturality X M s) ≫ Functor.whiskerLeft (associate X M Y) (Second.mapCell (F := X) (lastMapCell M m).as) := by
  apply NatTrans.ext
  funext z
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,eqToHom_app]
  change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
  rw [Category.comp_id,Category.id_comp]
  exact last_cell_app X M m z

end ContextualComposition.RelativeTensor.Iterated
