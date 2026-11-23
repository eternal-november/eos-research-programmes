module
public import ContextualComposition.RelativeTensorCrossingInterchange
public import ContextualComposition.RelativeTensorMixedMultiplication

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
universe v u vM uM vN uN vX uX vY uY
variable {B : Type u} [Category.{v} B]
variable {X X' : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX}} (t : X ⟶ X')
variable (M : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM}))
variable (N : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vN,uN}))
variable (Y : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vY,uY})

/-- Input change commutes with the complete exposed middle crossing on the fourfold quotient, for a possibly noninvertible crossing. -/
theorem exposedCrossing_input (s : middleComposite N M ⟶ middleComposite M N) :
    mapFirst (G := Y) (firstMap t (middleComposite N M)) ⋙ mapFirst (G := Y) (liftCrossing X' M N s) =
      mapFirst (G := Y) (liftCrossing X M N s) ⋙ mapFirst (G := Y) (firstMap t (middleComposite M N)) :=
  (First.map_composite (G := Y) (firstMap t (middleComposite N M)) (liftCrossing X' M N s)).symm.trans
    ((congrArg (fun k => mapFirst (G := Y) k) (crossingInterchange t s)).trans (First.map_composite _ _))

end ContextualComposition.RelativeTensor.Iterated
