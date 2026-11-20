module
public import ContextualComposition.RepresentableKleisliBicategory
public import ContextualComposition.RepresentableOriginalLastAssoc
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableKleisliCoherent
open CategoryTheory CategoryTheory.Bicategory
open AmbientCoherentPseudomonad RepresentableKleisliBicategory
open RepresentableKleisli
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
universe u
variable {B : Type u} [Category.{u} B] {P : Endpoints.{u,u,u,u} B} {S : P.Split} (T : Data S)
theorem actualLast : Last T := @RepresentableOriginalLastAssoc.original B _ P S T
theorem actualPent : Pent T := @RepresentableKleisliPentagon.original B _ P S T
@[instance_reducible]
noncomputable def bicategory : Bicategory (Part B) :=
  assemble T (actualLast T) (actualPent T)
end ContextualComposition.GrothendieckStep.RepresentableKleisliCoherent
