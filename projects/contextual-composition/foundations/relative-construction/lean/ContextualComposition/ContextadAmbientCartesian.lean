module
public import ContextualComposition.ContextadAmbientLift
public import ContextualComposition.ContextadExchangeData
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadAmbientPayload
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite FibreValue NativeCleavage
open ContextadWeakAction ContextadModification BoundaryPaste SpanApex TelescopeSquares
set_option backward.isDefEq.respectTransparency false
universe u v
variable {B : Type u} [Category.{v} B] {Y Z : Bᵒᵖ ⥤ Cat.{v,u}} (a : StrongTrans Y.toPseudofunctor' Z.toPseudofunctor')
theorem strongIsoPayload {x y : Total Y (𝟭 B)} (f : x ⟶ y) [IsIso (payloadMap f)] :
    IsIso (payloadMap ((totalStrong a).map f)) := by
  change IsIso ((a.app ⟨op (grade Y _ x)⟩).toFunctor.map (payloadMap f) ≫ (a.naturality (gradeMap f).op.toLoc).hom.toNatTrans.app _)
  infer_instance
theorem isoPayloadAligned {T : Type*} [Category* T] {e : T ⥤ B} {x y x' y' : Total Z e} {f : x ⟶ y} {g : x' ⟶ y'}
    (h : Aligned f g) [hg : IsIso (payloadMap g)] : IsIso (payloadMap f) := by
  obtain ⟨rfl,rfl,k⟩ := h; simp at k; exact k ▸ hg
variable {K : Type*} [Category* K] (e : K ⥤ B)
theorem liftPayload {x y : Total Y e} (f : x ⟶ y) [hf : IsIso (payloadMap f)] :
    IsIso (payloadMap ((atEndpoint a e).map f)) := by
  let l := second (projectionData Y) e
  have : IsIso (payloadMap (l.map f)) := hf
  letI : IsIso (payloadMap ((second (projectionData Y) e ⋙ totalStrong a).map f)) := strongIsoPayload a (l.map f)
  change IsIso (payloadMap (((atEndpoint a e ⋙ second (projectionData Z) e).map f)))
  exact isoPayloadAligned (e := 𝟭 B) (NativeCube.functorAlign (actionLeaf e (totalStrong a) (strongOver a)) f)
variable (p : K ⥤ B) (c : Cleavage p)
include c in
theorem liftCart : Pres (atEndpoint a e) (gradeProjection ⋙ p) (gradeProjection ⋙ p) := by
  apply ContextadCartesian.presOfChoice _ _ _ (extendChoice Y e p c)
  intro A z t
  let L := c A (grade Y e z) t
  let f := pullLift Y e z L.lift
  have : IsIso (payloadMap f) := (inferInstance : IsIso (𝟙 _))
  have : IsIso (payloadMap ((atEndpoint a e).map f)) := liftPayload a e f
  apply composite (ContextadCartesian.cart_of_payload Z e ((atEndpoint a e).map f))
  have h := NativeCube.functorAlign (actionGrade e (totalStrong a) (strongOver a)) f
  obtain ⟨s,d,k⟩ := h
  exact ContextadDisjointCut.cartAligned ⟨s,d,k⟩ L.cart
end ContextualComposition.GrothendieckStep.ContextadAmbientPayload
