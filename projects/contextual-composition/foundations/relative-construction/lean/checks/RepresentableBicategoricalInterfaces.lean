import ContextualComposition.RepresentableKleisliComparison
import ContextualComposition.RepresentableNativeCellColumns
open CategoryTheory CategoryTheory.Bicategory
open ContextualComposition.GrothendieckStep AmbientCoherentPseudomonad RepresentableKleisli
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
namespace RepresentableBicategoricalInterfaces
universe u
variable {B : Type u} [Category.{u} B] {P : Endpoints.{u,u,u,u} B} {S : P.Split} (T : Data S)
@[instance_reducible] noncomputable def bicategory := RepresentableKleisliCoherent.bicategory T
noncomputable def pseudofunctor := RepresentableKleisliComparison.embed T
set_option linter.defProp false in
def surjective := RepresentableKleisliComparison.covers T
set_option linter.defProp false in
def allLocal (A D : RepresentableKleisliComparison.Native T) := RepresentableKleisliComparison.localMap T A D
set_option linter.defProp false in
def binary (A D E : RepresentableKleisliBicategory.Part B) := RepresentableKleisliComparison.nativeComposition T A D E
set_option linter.defProp false in
def nativeUnit (A : RepresentableKleisliBicategory.Part B) := RepresentableKleisliComparison.nativeUnit T A
set_option linter.defProp false in
def lastOnArbitrary {A D E J : B} (f : KH S A D) (g : KH S D E) {h h' : KH S E J} (t : h ⟶ h') :=
  RepresentableOriginalLastAssoc.original T f g t
set_option linter.defProp false in
noncomputable def directedBending {A A' D D' : B} (u : A ⟶ A') (v : D ⟶ D') (f : KH S A D) (g : KH S A' D') :=
  RepresentableKleisliConstraints.bent T u v f g
end RepresentableBicategoricalInterfaces
#print axioms RepresentableBicategoricalInterfaces.bicategory
#print axioms RepresentableBicategoricalInterfaces.allLocal
#print axioms RepresentableBicategoricalInterfaces.binary
#print axioms RepresentableBicategoricalInterfaces.lastOnArbitrary
#print axioms RepresentableBicategoricalInterfaces.directedBending
