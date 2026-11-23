module
public import ContextualComposition.AmbientCellFunctor
public import ContextualComposition.RepresentableStrictEmbedding
public import ContextualComposition.PayloadLaws

@[expose] public section
namespace ContextualComposition.GrothendieckStep.WeightedAmbientPayload

open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite
open ContextadAmbientPayload ContextadWeakAction AmbientBlockCells AmbientCellFunctor
open AmbientRoundTrip ContextadModification FibreValue SpanApex BoundaryPaste
open scoped CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false

universe u v k w
variable {B : Type u} [Category.{v} B] {K : Type k} [Category.{w} K] (e : K ⥤ B)
variable {X Y Z : Bᵒᵖ ⥤ Cat.{v,u}}

/-- The weighted hom action uses the original total-category functor on strong maps and its directed lift on modifications. -/
noncomputable def homAction (Y Z : Bᵒᵖ ⥤ Cat.{v,u}) :
    (Y.toPseudofunctor' ⟶ Z.toPseudofunctor') ⥤ (Total Y e ⥤ Total Z e) where
  obj a := atEndpoint a e
  map m := endpointCell e m.as
  map_id a := endpointId e a
  map_comp f g := endpointComp f.as g.as e

theorem identity (Y : Bᵒᵖ ⥤ Cat.{v,u}) :
    (homAction e Y Y).obj (𝟙 Y.toPseudofunctor') = 𝟭 (Total Y e) := by
  unfold homAction atEndpoint
  simpa only [strongId] using (actionIdentity (Y := Y) e)

theorem comp (a : X.toPseudofunctor' ⟶ Y.toPseudofunctor') (b : Y.toPseudofunctor' ⟶ Z.toPseudofunctor') :
    (homAction e X Z).obj (a ≫ b) = (homAction e X Y).obj a ⋙ (homAction e Y Z).obj b :=
  atEndpointComp a b e

/-- The grade projection and unweighted payload component characterize the transported modification uniquely. -/
theorem cell_iff {a b : Y.toPseudofunctor' ⟶ Z.toPseudofunctor'} (m : a ⟶ b)
    (n : atEndpoint a e ⟶ atEndpoint b e) :
    n = (homAction e Y Z).map m ↔
      (∀ x, Pure (gradeMap (n.app x))) ∧
      (∀ x, (second (projectionData Z) e).map (n.app x) = (tail e m.as).app x) := by
  constructor
  · rintro rfl
    exact ⟨endpointOver e m.as,endpointLeaf e m.as⟩
  · rintro ⟨h,l⟩
    apply NatTrans.ext; funext x
    apply (intoPullback (projectionData Z) e).map_injective
    exact Limits.CategoricalPullback.hom_ext (pureEq (h x) (endpointOver e m.as x))
      ((l x).trans (endpointLeaf e m.as x).symm)

variable (t : Y ⟶ Z)

/-- A strict payload map preserves cartesian arrows of the unweighted total category. -/
theorem ordinaryCartesian : Pres (ChainPayload.fibreMap t (𝟭 B)) (proj Y) (proj Z) := by
  apply ContextadCartesian.presOfChoice _ _ _ (choice Y)
  intro A z f
  have p := ContextadPayloadModification.purePayload t (𝟭 B) ((choice Y A z f).lift) (pureId _)
  have : IsIso (payloadMap ((ChainPayload.fibreMap t (𝟭 B)).map ((choice Y A z f).lift))) := by
    obtain ⟨h,eq⟩ := p
    rw [eq]
    infer_instance
  exact ContextadCartesian.cart_of_payload Z (𝟭 B) _

/-- Decode the actual strict payload action using the existing cartesian-total/strong-map correspondence. -/
noncomputable def ordinary : Y.toPseudofunctor' ⟶ Z.toPseudofunctor' :=
  decodedStrong Y Z (ChainPayload.fibreMap t (𝟭 B)) rfl (ordinaryCartesian t)

theorem ordinary_total : totalStrong (ordinary t) = ChainPayload.fibreMap t (𝟭 B) :=
  encodeDecode Y Z (ChainPayload.fibreMap t (𝟭 B)) rfl (ordinaryCartesian t)

theorem ordinary_component (A : B) : ((ordinary t).app ⟨op A⟩).toFunctor = (t.app (op A)).toFunctor := by
  apply ContextadFinal.cancelIncl Z A
  have h := strongIncl (ordinary t) A
  rw [ordinary_total] at h
  exact h.trans (congrArg Functor.rightOp (EvalPayload.inclMapEq (ChainPayload.cell t (𝟭 B)) (op A)))

/-- The recovered ordinary comparison has exactly the equality transport dictated by naturality of the original map. -/
theorem ordinary_naturality {A D : B} (f : A ⟶ D) :
    ((ordinary t).naturality f.op.toLoc).hom.toNatTrans =
      eqToHom ((congrArg ((Y.map f.op).toFunctor ⋙ ·) (ordinary_component t A)).trans
        ((congrArg Cat.Hom.toFunctor (t.naturality f.op)).trans
          (congrArg (· ⋙ (Z.map f.op).toFunctor) (ordinary_component t D).symm))) := by
  apply NatTrans.ext; funext x
  apply pureEq
  · rw [← onLift]
    have h : ∀ F : Total Y (𝟭 B) ⥤ Total Z (𝟭 B), F = ChainPayload.fibreMap t (𝟭 B) →
        Pure (payloadMap (F.map (FibreValue.arrow Y f x))) := by
      rintro _ rfl
      exact ContextadPayloadModification.purePayload t _ _ (pureId _)
    exact h _ (ordinary_total t)
  · exact ⟨_,eqToHom_app _ _⟩

theorem ordinary_id (Y : Bᵒᵖ ⥤ Cat.{v,u}) : ordinary (𝟙 Y) = 𝟙 Y.toPseudofunctor' := by
  apply encodeInjective
  rw [ordinary_total, ChainPayload.fibreMap_id,strongId]

theorem ordinary_comp (s : X ⟶ Y) : ordinary (s ≫ t) = ordinary s ≫ ordinary t := by
  apply encodeInjective
  change totalStrong (ordinary (s ≫ t)) = totalStrong ((ordinary s).vcomp (ordinary t))
  rw [ordinary_total,ChainPayload.fibreMap_comp,strongComp,ordinary_total,ordinary_total]

/-- At any endpoint functor the ambient action restricts exactly to the ordinary weighted payload action, on the entire functor. -/
theorem on_ordinary : (homAction e Y Z).obj (ordinary t) = ChainPayload.fibreMap t e := by
  calc
    _ = action e (ChainPayload.fibreMap t (𝟭 B)) rfl := by
      have he {F H : Total Y (𝟭 B) ⥤ Total Z (𝟭 B)} (p : F ⋙ proj Z = proj Y)
          (q : H ⋙ proj Z = proj Y) (eq : F = H) : action e F p = action e H q := by
        subst H
        rfl
      exact he (strongOver (ordinary t)) rfl (ordinary_total t)
    _ = _ := onStrict e t

theorem on_weightedAction : ((homAction e Y Z).obj (ordinary t)).toCatHom = (PayloadLaws.weightedAction e).map t :=
  congrArg Functor.toCatHom (on_ordinary e t)

/-- Agreement with the previously defined identity-comparison embedding on its common-universe domain. -/
theorem ordinary_eq_existing {C : Type u} [Category.{u} C] {P Q : Cᵒᵖ ⥤ Cat.{u,u}} (f : P ⟶ Q) :
    ordinary f = RepresentableStrictEmbedding.strong f :=
  encodeInjective ((ordinary_total f).trans (RepresentableStrictEmbedding.encode f).symm)

end ContextualComposition.GrothendieckStep.WeightedAmbientPayload
