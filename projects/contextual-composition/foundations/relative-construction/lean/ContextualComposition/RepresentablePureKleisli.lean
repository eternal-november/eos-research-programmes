module
public import ContextualComposition.RepresentableKleisliConstraints
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentablePureKleisli
open CategoryTheory CategoryTheory.Bicategory
open AmbientBicategory AmbientCoherentPseudomonad RepresentableKleisli RepresentableKleisliConstraints RepresentableEndpointRealization
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
universe u
variable {B : Type u} [Category.{u} B] {P : Endpoints.{u,u,u,u} B} {S : P.Split} (T : Data S)
variable {A D E : B}
theorem identity (A : B) : pureK T (𝟙 A) = unit T A :=
  (congrArg (· ≫ unit T A) (RepresentablePure.pure_id A)).trans (AmbientBicategory.idComp.{u,u} (unit T A))
theorem pinTarget (u : A ⟶ D) (v : D ⟶ E) : target u (pureK T v) = pureK T (u ≫ v) :=
  (AmbientBicategory.compAssoc.{u,u} (pureMap u) (pureMap v) (unit T E)).symm.trans (congrArg (· ≫ unit T E) (RepresentablePure.pure_comp u v).symm)
noncomputable def comp (u : A ⟶ D) (v : D ⟶ E) : compose T (pureK T u) (pureK T v) ≅ pureK T (u ≫ v) :=
  preBend T u (pureK T v) ≪≫ eqToIso (pinTarget T u v)
end ContextualComposition.GrothendieckStep.RepresentablePureKleisli
