module
public import ContextualComposition.AmbientSquareBridge
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientIdentityOperation
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite TelescopeSquares FibreValue
open AmbientBicategory AmbientCoordinates ContextadModification NativeBlocks CategoryTheory.Bicategory
open ContextadRoutes ContextadNativeLaws ContextadOuterCharts AmbientHorizontalFrames ContextadLawTransport
open ContextadWeakAction ContextadWeakWeight ContextadAmbientPayload
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
universe u v
variable {B C : Type u} [Category.{v} B] [Category.{v} C]
variable {Y Z : Bᵒᵖ ⥤ Cat.{v,u}} (e : C ⥤ B) (a : StrongTrans Y.toPseudofunctor' Z.toPseudofunctor')
theorem tipPure (Y : Bᵒᵖ ⥤ Cat.{v,u}) (x : Total Y e) : Pure ((tip Y e e (𝟭 C) (𝟙 e)).app x) :=
  ContextadUnitTotal.pureTotal Y (𝟭 B) _ (pureId _) (pureId _)
theorem qPure (x : Total Y e) : Pure ((AmbientMateCalculus.q e e (𝟭 C) (𝟙 e) a).app x) := by
  let c := (AmbientMateCalculus.q e e (𝟭 C) (𝟙 e) a).app x
  let J := leafAt Z e
  let y := (atEndpoint a e).obj x
  have h : Pure (J.map c ≫ (tip Z e e (𝟭 C) (𝟙 e)).app y) :=
    AmbientMateCalculus.pureOfAligned (AmbientMateCalculus.factor e e (𝟭 C) (𝟙 e) a x) (pureMap _ (tipPure e Y x))
  obtain ⟨w,q⟩ := pureCancel h (tipPure e Z y)
  apply ContextadUnitTotal.pureTotal Z e _ (weakGrade e e (𝟭 C) (𝟙 e) a x)
  change Pure (payloadMap (J.map c))
  rw [q]; exact ContextadPayloadModification.pureCast _ _
section Native
variable {T : Type u} [Category.{max u v} T] {P : Endpoints.{u,max u v,u,max u v} T} (S : P.Split) {X Y : Obj.{u,v} T}
variable (i : Nat) (f : X ⟶ Y)
theorem boundary : AmbientBicategory.map S i f ≫ oper S (identity i) (fun _ h => h) Y = oper S (identity i) (fun _ h => h) X ≫ AmbientBicategory.map S i f := by
  rw [idRoute,idRoute,Category.id_comp,Category.comp_id]
theorem comparison : AmbientCoordinates.comparison S (identity i) (fun _ h => h) f = eqToIso (boundary S i f) :=
  AmbientOperationLaws.isoPure S _ _ (fun x => AmbientMateCalculus.pureOfAligned (AmbientComparisonRead.comparisonAt S (identity i) (fun _ h => h) f x) (qPure _ f.hom x))
end Native
end ContextualComposition.GrothendieckStep.AmbientIdentityOperation
