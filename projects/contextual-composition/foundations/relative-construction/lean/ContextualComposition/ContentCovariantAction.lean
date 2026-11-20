module
public import ContextualComposition.ContentCovariantOperations
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContentCovariantAction
open CategoryTheory CategoryTheory.Functor CategoryTheory.Bicategory Opposite
open AmbientBicategory AmbientCoherentPseudomonad ContentCovariantGrothendieck ContentCovariantOperations
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 850000
universe u
variable {B : Type u} [Category.{u} B] {P : Endpoints.{u,u,u,u} Bᵒᵖ} (S : P.Split)
variable {Y Z : Dual (B := B)} {f g : o Y ⟶ o Z}

/-- The component at A of the given ambient strong map, expressed in
the covariant integral chart. No strict-natural restriction on f. -/
noncomputable def arrow (f : o Y ⟶ o Z) (A : B) : Row P Y A ⥤ Row P Z A :=
  (fibre (S := S) Y A).inverse ⋙
    ((AmbientBicategory.map S 1 f).hom.app ⟨op (op A)⟩).toFunctor.op ⋙ (fibre (S := S) Z A).functor

/-- Arbitrary modifications. Reversing between fibre-opposite charts
does not invert the modification in the native covariant chart. -/
noncomputable def modification (t : g ⟶ f) (A : B) : arrow S f A ⟶ arrow S g A := by
  let q := NatTrans.op ((AmbientBicategory.cell S 1 t).hom.as.app ⟨op (op A)⟩).toNatTrans
  exact whiskerLeft (fibre (S := S) Y A).inverse (whiskerRight q (fibre (S := S) Z A).functor)

theorem strictArrow {Y Z : Dual (B := B)} (t : Y ⟶ Z) (A : B) :
    arrow S (InducedBicategory.mkHom (RepresentableStrictEmbedding.strong t)) A =
      (fibre (S := S) Y A).inverse ⋙ (ChainPayload.fibreMap t (P.extend (op A))).op ⋙ (fibre (S := S) Z A).functor := by
  exact congrArg (fun k => (fibre (S := S) Y A).inverse ⋙ k.op ⋙ (fibre (S := S) Z A).functor)
    (RepresentableKleisliOperations.layerStrict S t (op A))

end ContextualComposition.GrothendieckStep.ContentCovariantAction
