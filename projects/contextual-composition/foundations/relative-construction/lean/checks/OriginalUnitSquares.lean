import ContextualComposition.AmbientLeftSquare
import ContextualComposition.AmbientRightSquare
open CategoryTheory CategoryTheory.Bicategory ContextualComposition.GrothendieckStep
open AmbientBicategory AmbientHorizontalNaturality ContextadNativeLaws
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
namespace OriginalUnitSquares
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (d : ContextadUnit.Data P) (m : ContextadTotal.Native S) (C : Constraints d m)
variable {X Y : Obj.{u,v} B} (f : X ⟶ Y)
theorem both : Left S d m C f ∧ Right S d m C f :=
  ⟨AmbientLeftSquare.original f d m C,AmbientRightSquare.original f d m C⟩
end OriginalUnitSquares
#print axioms OriginalUnitSquares.both
