module
public import ContextualComposition.TelescopeAmbientComponents
public import ContextualComposition.WeightedAmbientPayload

@[expose] public section
namespace ContextualComposition.GrothendieckStep.TelescopeAmbientLaws
open CategoryTheory CategoryTheory.Functor Opposite
open FibreValue NativeCleavage CoproductSpan CoproductSpan.All ContextadAmbientPayload AmbientBicategory
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B}
variable (S : P.Split) (A : B) {X Y Z : Obj.{u,v} B}

noncomputable def whole (f : X ⟶ Y) := atEndpoint f.hom (wholeLeg (src S) (dst S) A)
noncomputable def leaves (f : X ⟶ Y) := ZeroPower.Sum.map (fun n => atEndpoint f.hom (leg (src S) (dst S) A n))
noncomputable def iterates (f : X ⟶ Y) := ZeroPower.Sum.map (TelescopeAmbientComponents.target (X := X) (Y := Y) S A f)

theorem wholeId (X : Obj.{u,v} B) : whole S A (𝟙 X) = 𝟭 _ :=
  WeightedAmbientPayload.identity _ (underlying X)

theorem wholeComp (f : X ⟶ Y) (g : Y ⟶ Z) : whole S A (f ≫ g) = whole S A f ⋙ whole S A g :=
  atEndpointComp f.hom g.hom _

theorem leafId (X : Obj.{u,v} B) : leaves S A (𝟙 X) = 𝟭 _ :=
  (congrArg ZeroPower.Sum.map (funext fun n => WeightedAmbientPayload.identity (leg (src S) (dst S) A n) (underlying X))).trans PayloadLaws.sumId

theorem leafComp (f : X ⟶ Y) (g : Y ⟶ Z) : leaves S A (f ≫ g) = leaves S A f ⋙ leaves S A g :=
  (congrArg ZeroPower.Sum.map (funext fun n => atEndpointComp f.hom g.hom (leg (src S) (dst S) A n))).trans (PayloadLaws.sumComp _ _)

theorem iterateId (X : Obj.{u,v} B) : iterates S A (𝟙 X) = 𝟭 _ := by
  apply Eq.trans _ PayloadLaws.sumId
  apply congrArg ZeroPower.Sum.map
  funext n
  exact congrArg (fun m => AmbientRoundTrip.compAt m A) (AmbientBlockIteration.blockId S (underlying X) n)

theorem iterateComp (f : X ⟶ Y) (g : Y ⟶ Z) : iterates S A (f ≫ g) = iterates S A f ⋙ iterates S A g := by
  apply Eq.trans _ (PayloadLaws.sumComp _ _)
  apply congrArg ZeroPower.Sum.map
  funext n
  exact congrArg (fun m => AmbientRoundTrip.compAt m A) (AmbientBlockIteration.blockComp S f.hom g.hom n)

noncomputable def forward (f : X ⟶ Y) :
    (PayloadLaws.All.presentation S A (underlying X)).functor ⋙ whole S A f ≅ leaves S A f ⋙ (PayloadLaws.All.presentation S A (underlying Y)).functor :=
  eqToIso (TelescopeGradeChange.compare_payload f.hom (src S) (dst S) A)
noncomputable def tagged (f : X ⟶ Y) :=
  SumChange.Tagged.square (fun n => (component S (underlying X) A n).functor)
    (fun n => (component S (underlying Y) A n).functor)
    (fun n => atEndpoint f.hom (leg (src S) (dst S) A n)) (TelescopeAmbientComponents.target (X := X) (Y := Y) S A f)
    (fun n => eqToIso (TelescopeAmbientComponents.component_payload S A f n))

theorem forwardTransport (f : X ⟶ Y) (x) : ForwardMixed.IsTransport ((forward S A f).inv.app x) :=
  ForwardMixed.IsTransport.app (TelescopeGradeChange.compare_payload f.hom (src S) (dst S) A).symm x

theorem taggedTransport (f : X ⟶ Y) (x) : ForwardMixed.IsTransport ((tagged S A f).inv.app x) := by
  rcases x with ⟨n,x⟩
  exact (ForwardMixed.IsTransport.app (TelescopeAmbientComponents.component_payload S A f n).symm x).map (Sigma.incl n)

end ContextualComposition.GrothendieckStep.TelescopeAmbientLaws
