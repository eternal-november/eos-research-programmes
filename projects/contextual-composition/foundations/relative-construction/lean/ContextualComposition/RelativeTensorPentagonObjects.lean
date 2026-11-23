module
public import ContextualComposition.RelativeTensorPentagonCoordinates

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
universe vB uB vC uC vD uD vX uX vM uM vN uN vY uY
variable {B : Type uB} {C : Type uC} {D : Type uD} [Category.{vB} B] [Category.{vC} C] [Category.{vD} D]
variable (X : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX})
variable (M : LocallyDiscrete C ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM}))
variable (N : LocallyDiscrete D ⥤ᵖ (LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vN,uN}))
variable (Y : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{vY,uY})
variable (V : rightInner (middleComposite M N) Y ⟶ rightInner M (rightInner N Y))

abbrev routeWith := (firstPentagonEdge X M N Y ⋙ associate X (middleComposite M N) Y) ⋙ mapSecond (F := X) V

variable (rowComponent : ∀ b : B, Second.part V b = OuterRow.direct M N Y ⟨op b⟩)

include rowComponent in
theorem route_objects (z : farLeft X M N Y) : (twoStep X M N Y).functor.obj z = (routeWith X M N Y V).obj z := by
  obtain ⟨⟨d,⟨⟨c,⟨⟨b,x,m⟩⟩,n⟩⟩,y⟩⟩ := z
  let z := (insertM (middleComposite M N) Y b d).obj ((insertion (row M b) (column N d) c).obj (m,n),y)
  exact congrArg (fun k => (insertR X M (rightInner N Y) b).obj (x,k)) (Functor.congr_obj (rowComponent b).symm z)

end ContextualComposition.RelativeTensor.Iterated
