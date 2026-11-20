module
public import ContextualComposition.RepresentableKleisliData
public import ContextualComposition.AmbientOperationBoundaries
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableStrictEmbedding
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite CategoryTheory.Bicategory
open FibreValue ContextadCoherence ContextadAmbientPayload AmbientRoundTrip
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
universe u
variable {B : Type u} [Category.{u} B] {G H : Bᵒᵖ ⥤ Cat.{u,u}}
variable (t : G ⟶ H)
def square {A D : B} (a : D ⟶ A) :
    (G.map a.op).toFunctor ⋙ (t.app (op D)).toFunctor ≅ (t.app (op A)).toFunctor ⋙ (H.map a.op).toFunctor :=
  eqToIso (congrArg Cat.Hom.toFunctor (t.naturality a.op))
theorem squarePure {A D : B} (a : D ⟶ A) (x : G.obj (op A)) : Pure ((square t a).hom.app x) :=
  RepresentableYoneda.pureFrame _ x
def strong : StrongTrans G.toPseudofunctor' H.toPseudofunctor' :=
  ContextadStrong.assemble (G := G) (H := H) (fun A => (t.app (op A)).toFunctor) (square t)
    (fun D f => pureEq (pureComp (squarePure t (𝟙 D) f) ⟨_,eqToHom_app _ _⟩) (pureMap _ ⟨_,eqToHom_app _ _⟩))
    (fun a b f => pureEq (pureComp (squarePure t (a ≫ b) f) ⟨_,eqToHom_app _ _⟩)
      (pureComp (pureMap _ ⟨_,eqToHom_app _ _⟩) (pureComp (squarePure t a _) (pureMap _ (squarePure t b f)))))
theorem encode : totalStrong (strong t) = ChainPayload.fibreMap t (𝟭 B) := by
  apply ContextadUnitTotal.normalUnique G H _ _ (strongOver (strong t)) rfl
  · intro A
    exact (strongIncl (strong t) A).symm.trans (ContextadPayloadModification.inclSquare t A).symm
  · intro z A a
    have e := onLift (strong t) a (payload G (𝟭 B) z)
    change Pure (payloadMap ((totalStrong (strong t)).map (FibreValue.arrow G a (payload G _ z))))
    rw [e]
    exact squarePure t a (payload G _ z)
  · intro z A a
    exact ContextadPayloadModification.purePayload t _ _ (pureId _)
variable {A : B} (x : H.obj (op A))
def strictExtension : RepresentableYoneda.rep A ⟶ H where
  app D := (RepresentableYoneda.extendAt H A x D.unop).toCatHom
  naturality _ _ a := congrArg Functor.toCatHom (RepresentableYoneda.extendSquareEq H A x a.unop)
theorem readsExtension : strong (strictExtension x) = RepresentableYoneda.extend H A x := by
  apply AmbientRoundTrip.strongExt
  · rfl
  · intro D E a f
    rfl
end ContextualComposition.GrothendieckStep.RepresentableStrictEmbedding
