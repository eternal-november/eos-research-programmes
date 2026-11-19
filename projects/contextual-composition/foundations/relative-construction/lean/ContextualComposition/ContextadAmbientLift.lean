module
public import ContextualComposition.ContextadAmbientPayload
public import ContextualComposition.ContextadWeakAction
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadAmbientPayload
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite FibreValue
open scoped CategoryTheory.Bicategory
open CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
universe u v
variable {B : Type u} [Category.{v} B] (Y : Bᵒᵖ ⥤ Cat.{v,u})
theorem readWriteFunctor : read Y ⋙ write Y = 𝟭 _ := rfl
theorem writeReadFunctor : write Y ⋙ read Y = 𝟭 _ := rfl
variable {Y} {Z W : Bᵒᵖ ⥤ Cat.{v,u}}
variable (a : StrongTrans Y.toPseudofunctor' Z.toPseudofunctor') (b : StrongTrans Z.toPseudofunctor' W.toPseudofunctor')
def totalStrong := read Y ⋙ CoGrothendieck.map a ⋙ write Z
theorem strongOver : totalStrong a ⋙ proj Z = proj Y := rfl
theorem strongId : totalStrong (𝟙 Y.toPseudofunctor') = 𝟭 _ := by
  unfold totalStrong; rw [CoGrothendieck.map_id_eq]; exact readWriteFunctor Y
theorem strongComp : totalStrong (a.vcomp b) = totalStrong a ⋙ totalStrong b := by
  unfold totalStrong; rw [show CoGrothendieck.map (a.vcomp b) = _ from CoGrothendieck.map_comp_eq (F := Y.toPseudofunctor') (G := Z.toPseudofunctor') (H := W.toPseudofunctor') a b]
  rfl
theorem strongCart : ContextadModification.Pres (totalStrong a) (proj Y) (proj Z) := by
  apply ContextadCartesian.presOfChoice (totalStrong a) (proj Y) (proj Z) (choice Y)
  intro A z t
  have h : IsIso (payloadMap ((totalStrong a).map ((choice Y A z t).lift))) := by
    change IsIso ((a.app ⟨op A⟩).toFunctor.map (𝟙 _) ≫ (a.naturality t.op.toLoc).hom.toNatTrans.app _)
    rw [Functor.map_id,Category.id_comp]
    infer_instance
  exact ContextadCartesian.cart_of_payload Z (𝟭 B) _
variable {K : Type*} [Category* K] (e : K ⥤ B)
noncomputable def atEndpoint := ContextadWeakAction.action e (totalStrong a) (strongOver a)
theorem atEndpointComp : atEndpoint (a.vcomp b) e = atEndpoint a e ⋙ atEndpoint b e := by
  unfold atEndpoint; rw [ContextadWeakAction.actionComp]; congr 1; exact strongComp a b
end ContextualComposition.GrothendieckStep.ContextadAmbientPayload
