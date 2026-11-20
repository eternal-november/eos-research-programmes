import ContextualComposition.AmbientCoherentObserver
open CategoryTheory CategoryTheory.Pseudofunctor CategoryTheory.Bicategory
open ContextualComposition.GrothendieckStep AmbientBicategory ContextadNativeLaws
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
namespace OriginalCoherentInterface
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (d : ContextadUnit.Data P) (m : ContextadTotal.Native S) (C : Constraints d m)
variable {X Y : Obj.{u,v} B} (f : X ⟶ Y)
theorem noPolygonAssumed : AmbientHorizontalNaturality.Left S d m C f ∧ AmbientHorizontalNaturality.Right S d m C f ∧ AmbientHorizontalNaturality.Assoc S d m C f :=
  ⟨AmbientLeftSquare.original f d m C,AmbientRightSquare.original f d m C,AmbientAssociativity.original f m d C⟩
theorem yesIff : ContextadSchedule.Coherent d m C ↔ AmbientCoherentPseudomonad.Laws S d m C := AmbientCoherentObserver.exactCriterion d m C
variable (h : ContextadSchedule.Coherent d m C)
noncomputable def center := AmbientCoherentPseudomonad.build d m C h
noncomputable def eta : StrongTrans (AmbientMonadMaps.II (B := B)) (AmbientMonadMaps.K S) := AmbientCoherentPseudomonad.unitMap (center d m C h)
noncomputable def mu : StrongTrans (AmbientMonadMaps.KK S) (AmbientMonadMaps.K S) := AmbientCoherentPseudomonad.multMap (center d m C h)
variable (Z : Obj.{u,v} B)
include h in
theorem originalFaces : AmbientHorizontalDiagrams.Triangle S d m C Z ∧ AmbientHorizontalDiagrams.Pentagon S d m C Z :=
  ⟨(center d m C h).laws.triangle Z,(center d m C h).laws.pentagon Z⟩
end OriginalCoherentInterface
#print axioms OriginalCoherentInterface.yesIff
#print axioms OriginalCoherentInterface.originalFaces
