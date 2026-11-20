module
public import ContextualComposition.AmbientConstraintIsos
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientPseudomonadProjections
open CategoryTheory CategoryTheory.Pseudofunctor CategoryTheory.Bicategory
open AmbientBicategory AmbientMonadMaps AmbientCoherentPseudomonad
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 750000
universe u v
local instance instHom {L : Type*} [Bicategory L] {M : Type*} [Bicategory M] (F G : Pseudofunctor L M) : Category (StrongTrans F G) := StrongTrans.homCategory
section General
variable {C D : Type*} [Bicategory C] [Bicategory D]
variable {F G : StrictPseudofunctor C D} {K : Pseudofunctor C D} (e : F = G)
variable {a b : StrongTrans F.toPseudofunctor K} (i : a ≅ b)
def transferIso : transfer e a ≅ transfer e b := by cases e; exact i
theorem transportedApp (X : C) : HEq ((transferIso e i).hom.as.app X) (i.hom.as.app X) := by cases e; rfl
end General
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split)
noncomputable abbrev three := ((action S 1).comp (action S 1)).comp (action S 1)
theorem fixedPower : action S 3 = three.{u,v} S :=
  (AmbientIteratedFunctor.succ S 2).symm.trans (congrArg (fun F => F.comp (action S 1)) (AmbientIteratedFunctor.succ S 1).symm)
variable {S} (T : Data S)
noncomputable def leftModification := AmbientConstraintIsos.left T.unit T.mult T.constraints
noncomputable def rightModification := AmbientConstraintIsos.right T.unit T.mult T.constraints
noncomputable def assocModification := transferIso (F := action S 3) (G := three S) (K := AmbientMonadMaps.K S)
  (fixedPower S) (AmbientConstraintIsos.assoc T.unit T.mult T.constraints)
set_option linter.defProp false in
def assocApp (Z : Obj.{u,v} B) :=
  (transportedApp (F := action S 3) (G := three S) (K := AmbientMonadMaps.K S) (fixedPower S)
  (AmbientConstraintIsos.assoc T.unit T.mult T.constraints) Z).trans (heq_of_eq (AmbientConstraintIsos.assocApp T.unit T.mult T.constraints Z))
end ContextualComposition.GrothendieckStep.AmbientPseudomonadProjections
