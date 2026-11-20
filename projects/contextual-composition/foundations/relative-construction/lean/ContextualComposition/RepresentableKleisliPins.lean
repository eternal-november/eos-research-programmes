module
public import ContextualComposition.RepresentableKleisliOperations
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableKleisli
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite CategoryTheory.Bicategory
open AmbientBicategory AmbientHorizontalFrames AmbientCoherentPseudomonad RepresentableKleisliOperations
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 750000
universe u
variable {B : Type u} [Category.{u} B] {P : Endpoints.{u,u,u,u} B} {S : P.Split}
variable {A D E : B}
def canonical (x : RepresentableComma.Row (P.extend A) D) : KH S A D :=
  InducedBicategory.mkHom (RepresentableYoneda.extend (underlying.{u,u} (KObj S D)) A x)
def canonStrict (x : RepresentableComma.Row (P.extend A) D) : RepresentableYoneda.rep A ⟶ underlying.{u,u} (KObj S D) :=
  RepresentableStrictEmbedding.strictExtension x
theorem canon_eq (x : RepresentableComma.Row (P.extend A) D) :
    (canonical (S := S) x).hom = RepresentableStrictEmbedding.strong (canonStrict (S := S) x) :=
  (RepresentableStrictEmbedding.readsExtension (A := A) (H := underlying.{u,u} (KObj S D)) x).symm
def pureMap (u : A ⟶ D) : yObj A ⟶ yObj D :=
  InducedBicategory.mkHom (RepresentableYoneda.extend (RepresentableYoneda.rep D) A (Discrete.mk u))
theorem pureAt (u : A ⟶ D) {J : B} (f : J ⟶ A) :
    RepresentableYoneda.atPoint (RepresentableYoneda.rep D) A (pureMap u).hom f = Discrete.mk (f ≫ u) := rfl
noncomputable def pureK (T : Data S) (u : A ⟶ D) : KH S A D := pureMap u ≫ unit T D
theorem pureKAt (T : Data S) (u : A ⟶ D) :
    row (pureK T u) = pair (RepresentableYoneda.rep D) (P.extend A) (T.unit.grade A)
      (Discrete.mk (T.unit.discharge A ≫ u)) := by
  change (AmbientRoundTrip.compAt (E S (yObj D) T.unit).hom A).obj
    ((AmbientRoundTrip.compAt (pureMap u).hom A).obj (Discrete.mk (𝟙 A))) = _
  -- The unit is applied at the source object A; the final operation is still the one at yD.
  rw [unitAt T (yObj D) A]
  change pair (RepresentableYoneda.rep D) (P.extend A) (T.unit.grade A) (Discrete.mk (T.unit.discharge A ≫ (𝟙 A ≫ u))) = _
  rw [Category.id_comp]
theorem identityAt (T : Data S) (A : B) :
    row (unit T A) = pair (RepresentableYoneda.rep A) (P.extend A) (T.unit.grade A)
      (Discrete.mk (T.unit.discharge A)) := by
  change (AmbientRoundTrip.compAt (E S (yObj A) T.unit).hom A).obj (Discrete.mk (𝟙 A)) = _
  rw [unitAt T (yObj A) A]
  change pair (RepresentableYoneda.rep A) (P.extend A) (T.unit.grade A) (Discrete.mk (T.unit.discharge A ≫ 𝟙 A)) = _
  rw [Category.comp_id]
end ContextualComposition.GrothendieckStep.RepresentableKleisli
