module
public import ContextualComposition.AmbientBoundaryReduction
public import ContextualComposition.AmbientInsideMateRead
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientObservationChart
open CategoryTheory CategoryTheory.Functor Opposite FibreValue TelescopeSquares
open ContextadAmbientPayload ContextadWeakAction AmbientBicategory AmbientCoordinates ContextadRoutes
open ContextadModification NativeBlocks CategoryTheory.Bicategory ContextadLawTransport ContextadOuterCharts SpanApex
open AmbientHorizontalFrames AmbientHorizontalDiagrams ContextadWeakWeight AmbientBoundaryReduction
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
universe u v
section General
variable {A B C D E F : Type*} [Category* A] [Category* B] [Category* C] [Category* D] [Category* E] [Category* F]
theorem peel (I : A ⥤ C) (V : B ⥤ D) (V' : E ⥤ D) [I.IsIso] [V.IsIso] [V'.IsIso]
    (J : B ⥤ E) (H : E ⥤ F) (v : J ⋙ V' = V) {T W : C ⥤ D} (n : T ⟶ W)
    (h : ∀ x, Pure (H.map (V'.strictInv.map (n.app (I.obj x))))) (y : C) :
    Pure ((J ⋙ H).map (V.strictInv.map (n.app y))) := by
  have vz : V.strictInv ⋙ J = V'.strictInv :=
    by
      apply V.asIsomorphism.functor_comp_injective
      exact (ContextadRecognition.eraseInv V J).trans ((congrArg (· ⋙ V'.strictInv) v.symm).trans (congrArg (J ⋙ ·) V'.asIsomorphism.unit_eq.symm)).symm
  have z := (NativeCube.functorAlign vz (n.app y)).map H
  apply AmbientMateCalculus.pureOfAligned z
  apply AmbientMateCalculus.pureOfAligned (((ContextadPayloadModification.appChange n (Functor.congr_obj I.asIsomorphism.counit_eq.symm y)).map V'.strictInv).map H)
  exact h _
end General
section Target
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split} (X : Obj.{u,v} B)
variable {A C : Type*} [Category* A] [Category* C] (I : A ⥤ C) [I.IsIso]
theorem headOfNested {T W : C ⥤ Total (underlying (obj S 2 X)) (𝟭 B)} (n : T ⟶ W)
    (h : ∀ x, Pure (gradeMap ((chart S (obj S 1 X) 1).strictInv.map (n.app (I.obj x))))) (y : C) :
    Pure (gradeMap (gradeMap ((chart S X 2).strictInv.map (n.app y)))) := by
  let z := (chart S X 2).strictInv.map (n.app y)
  apply AmbientMateCalculus.pureOfAligned (NativeCube.functorAlign (stageHead (S := S) (underlying X) (power S 1)).symm z)
  exact peel I (chart S X 2) (chart S (obj S 1 X) 1) (stage (S := S) (underlying X) (power S 1)) gradeProjection
    (resolve1 (S := S) X) n h y
end Target
end ContextualComposition.GrothendieckStep.AmbientObservationChart
