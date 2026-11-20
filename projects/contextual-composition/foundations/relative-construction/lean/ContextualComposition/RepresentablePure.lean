module
public import ContextualComposition.RepresentableKleisliPins
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentablePure
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite CategoryTheory.Bicategory
open AmbientBicategory RepresentableKleisli RepresentableStrictEmbedding ContextadAmbientPayload
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
universe u
variable {B : Type u} [Category.{u} B] {A D E : B}
abbrev R (A : B) := RepresentableYoneda.rep A
def strictMap (a : A ⟶ D) : R A ⟶ R D := whiskerRight (CategoryTheory.yoneda.map a) typeToCat
theorem strictComp (a : A ⟶ D) (b : D ⟶ E) : strictMap (a ≫ b) = strictMap a ≫ strictMap b := by
  change ((whiskeringRight Bᵒᵖ _ _).obj typeToCat).map (CategoryTheory.yoneda.map (a ≫ b)) = _
  rw [Functor.map_comp,Functor.map_comp]; rfl
theorem strictId (A : B) : strictMap (𝟙 A) = 𝟙 (R A) := by
  change ((whiskeringRight Bᵒᵖ _ _).obj typeToCat).map (CategoryTheory.yoneda.map (𝟙 A)) = _
  rw [Functor.map_id,Functor.map_id]; rfl
theorem strictPin (a : A ⟶ D) : strictMap a = strictExtension (H := R D) (Discrete.mk a) := by
  apply NatTrans.ext
  funext J
  apply congrArg Functor.toCatHom
  fapply Functor.ext
  · intro _; rfl
  · intro x y f
    exact Subsingleton.elim _ _
theorem compStrict {Y Z W : Bᵒᵖ ⥤ Cat.{u,u}} (t : Y ⟶ Z) (s : Z ⟶ W) : strong (t ≫ s) = (strong t).vcomp (strong s) := by
  apply AmbientRoundTrip.encodeInjective
  rw [strongComp, encode,encode,encode,ChainPayload.fibreMap_comp]
theorem idStrict (Y : Bᵒᵖ ⥤ Cat.{u,u}) : strong (𝟙 Y) = StrongTrans.id Y.toPseudofunctor' := by
  apply AmbientRoundTrip.encodeInjective
  exact (encode _).trans ((ChainPayload.fibreMap_id _).trans (strongId (Y := Y)).symm)
theorem pin (a : A ⟶ D) : (pureMap a).hom = strong (strictMap a) :=
  (readsExtension (A := A) (H := R D) (Discrete.mk a)).symm.trans (congrArg strong (strictPin a).symm)
theorem pure_id (A : B) : pureMap (𝟙 A) = 𝟙 (yObj A) := by
  apply InducedBicategory.hom_ext
  rw [pin,strictId,idStrict]; rfl
theorem pure_comp (a : A ⟶ D) (b : D ⟶ E) : pureMap (a ≫ b) = pureMap a ≫ pureMap b := by
  apply InducedBicategory.hom_ext
  change (pureMap (a ≫ b)).hom = (pureMap a).hom.vcomp (pureMap b).hom
  rw [pin,pin,pin,strictComp,compStrict]
end ContextualComposition.GrothendieckStep.RepresentablePure
