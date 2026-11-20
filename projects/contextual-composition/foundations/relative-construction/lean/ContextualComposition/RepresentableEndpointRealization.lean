module
public import ContextualComposition.RepresentablePure
public import ContextualComposition.RepresentableNativeEndpoints
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableEndpointRealization
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite CategoryTheory.Bicategory
open AmbientBicategory RepresentableKleisli RepresentableKleisliOperations RepresentableNativeEndpoints
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 950000
universe u
variable {B : Type u} [Category.{u} B] {P : Endpoints.{u,u,u,u} B} {S : P.Split}
variable {A D A' D' : B}
noncomputable def source (v : D ⟶ D') (f : KH S A D) : KH S A D' := f ≫ AmbientBicategory.map S 1 (pureMap v)
noncomputable def target (u : A ⟶ A') (g : KH S A' D') : KH S A D' := pureMap u ≫ g
theorem sourceFormula (v : D ⟶ D') (f : KH S A D) : row (source v f) = post v (row f) := by
  change (AmbientRoundTrip.compAt (ContextadAmbientPayload.blockStrong (S := S) (pureMap v).hom 1) A).obj (row f) = _
  rw [RepresentablePure.pin,layerStrict]
  rfl
noncomputable def preAt (u : A ⟶ A') (g : KH S A' D') : row (target u g) ≅ pre u (row g) :=
  eqToIso (congrArg (RepresentableYoneda.atPoint (underlying.{u,u} (KObj S D')) A' g.hom) (Category.id_comp u)) ≪≫
    RepresentableYoneda.counitAt g.hom u
def across {C : Type*} [Category C] {x x' y y' : C} (a : x ≅ x') (b : y ≅ y') : (x ⟶ y) ≃ (x' ⟶ y') where
  toFun h := a.inv ≫ h ≫ b.hom
  invFun h := a.hom ≫ h ≫ b.inv
  left_inv h := by simp
  right_inv h := by simp
noncomputable def realization (u : A ⟶ A') (v : D ⟶ D') (f : KH S A D) (g : KH S A' D') :
    (source v f ⟶ target u g) ≃ Square u v (row f) (row g) :=
  ((fibreEquiv (S := S) (A := A) (D := D')).fullyFaithfulFunctor.homEquiv).trans <|
    (across (eqToIso (sourceFormula v f)) (preAt u g)).trans (edgeEquiv u v (row f) (row g))
end ContextualComposition.GrothendieckStep.RepresentableEndpointRealization
