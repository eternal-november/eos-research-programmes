import ContextualComposition.RepresentableNativeCellColumns
import ContextualComposition.RepresentableCommaComposition
import ContextualComposition.RepresentablePureKleisli
import ContextualComposition.RepresentableLeftUnitor
import ContextualComposition.RepresentableKleisliTriangle
import ContextualComposition.RepresentablePentagonCorner
import ContextualComposition.RepresentableAssociatorPrefix
import ContextualComposition.RepresentableRestrictionBoundary
open CategoryTheory CategoryTheory.Functor CategoryTheory.Bicategory
open ContextualComposition.GrothendieckStep RepresentableKleisli AmbientCoherentPseudomonad
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
namespace RepresentableInterfaces
universe u
variable {B : Type u} [Category.{u} B] {P : Endpoints.{u,u,u,u} B} {S : P.Split} (T : Data S)
variable {A D E : B}
def localAt : KH S A D ≌ CostructuredArrow (P.extend A) D := commaEquiv
noncomputable def left (f : KH S A D) := RepresentableKleisliConstraints.leftUnit T f
noncomputable def mixed (f : KH S A D) (g : KH S D E) := RepresentableNativeComposition.atArbitrary T f g
noncomputable def directedPaste (f : KH S A D) (g : KH S A E) (v : D ⟶ E) :=
  RepresentableKleisliConstraints.bent T (𝟙 A) v f g
set_option linter.defProp false in
def bothColumns {f f' : KH S A D} {g g' : KH S D E} (t : f ⟶ f') (k : g ⟶ g') :=
  RepresentableCompositionCells.actualCell T t k
set_option linter.defProp false in
def actualTriangle (f : KH S A D) (g : KH S D E) := RepresentableKleisliTriangle.original T f g
set_option linter.defProp false in
def firstAssociator {f f' : KH S A D} (t : f ⟶ f') (g : KH S D E) (h : KH S E E) :=
  RepresentableAssociatorPrefix.original T t g h
theorem limit (A : B) : ¬ Nonempty (yObj A ⟶ AmbientBicategory.obj S 1 (RepresentableRestrictionBoundary.empty (B := B))) :=
  RepresentableRestrictionBoundary.emptyK S A
end RepresentableInterfaces
#print axioms RepresentableInterfaces.localAt
#print axioms RepresentableInterfaces.directedPaste
#print axioms RepresentableInterfaces.bothColumns
#print axioms RepresentableInterfaces.actualTriangle
#print axioms RepresentableInterfaces.firstAssociator
