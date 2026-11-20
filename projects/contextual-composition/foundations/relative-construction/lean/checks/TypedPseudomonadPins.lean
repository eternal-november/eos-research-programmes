import ContextualComposition.AmbientLiteralMonadMaps
import ContextualComposition.AmbientConstraintIdentifications
open CategoryTheory CategoryTheory.Pseudofunctor CategoryTheory.Bicategory
open ContextualComposition.GrothendieckStep AmbientBicategory AmbientCoherentPseudomonad
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
namespace TypedPseudomonadPins
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
local instance instHom {L : Type*} [Bicategory L] {M : Type*} [Bicategory M] (F G : Pseudofunctor L M) : Category (StrongTrans F G) := StrongTrans.homCategory
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (T : Data S) (X : Obj.{u,v} B)
theorem leftPin : (AmbientPseudomonadProjections.leftModification T).hom.as.app X = (leftIso T X).hom := AmbientConstraintIsos.leftApp T.unit T.mult T.constraints X
theorem rightPin : (AmbientPseudomonadProjections.rightModification T).hom.as.app X = (rightIso T X).hom := AmbientConstraintIsos.rightApp T.unit T.mult T.constraints X
set_option linter.defProp false in
def assocPin := AmbientPseudomonadProjections.assocApp T X
#check @AmbientConstraintIdentifications.outerUnit
#check @AmbientConstraintIdentifications.innerUnit
#check @AmbientConstraintIdentifications.identity
#check @AmbientConstraintIdentifications.first
#check @AmbientConstraintIdentifications.last
#check @AmbientLiteralMonadMaps.mu
end TypedPseudomonadPins
#print axioms TypedPseudomonadPins.assocPin
