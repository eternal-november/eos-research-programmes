module
public import ContextualComposition.ContextadAmbientCartesian
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadWeakWeight
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite FibreValue NativeCleavage
open ContextadWeakAction ContextadModification BoundaryPaste SpanApex TelescopeSquares ContextadOuterCharts ContextadAmbientPayload ContextadDisjointCut
set_option backward.isDefEq.respectTransparency false
universe u v
variable {B K L : Type u} [Category.{v} B] [Category.{v} K] [Category.{v} L] (Y : Bᵒᵖ ⥤ Cat.{v,u}) (e : K ⥤ B) (d : L ⥤ B)
variable (r : K ⥤ L) (δ : r ⋙ d ⟶ e)
abbrev leafAt := second (projectionData Y) e
def tip : restrict Y e d r δ ⋙ leafAt Y d ⟶ leafAt Y e :=
  NatTrans.op (ContextadRoutes.preCell (Y ⋙ Cat.opFunctor) (NatTrans.op δ))
theorem tipCart (x) : Cartesian (proj Y) ((tip Y e d r δ).app x) := cartesianLift Y (𝟭 B) _ _
theorem tipBase (x) : (proj Y).map ((tip Y e d r δ).app x) = δ.app (grade Y e x) := rfl
variable {Y} {Z : Bᵒᵖ ⥤ Cat.{v,u}} (a : StrongTrans Y.toPseudofunctor' Z.toPseudofunctor')
noncomputable abbrev lRoute := restrict Y e d r δ ⋙ atEndpoint a d
noncomputable abbrev rRoute := atEndpoint a e ⋙ restrict Z e d r δ
theorem sameGrade : lRoute e d r δ a ⋙ gradeProjection = rRoute e d r δ a ⋙ gradeProjection := by
  change restrict Y e d r δ ⋙ action d _ _ ⋙ gradeProjection = (atEndpoint a e ⋙ gradeProjection) ⋙ r
  rw [actionGrade,show atEndpoint a e ⋙ gradeProjection = _ from actionGrade e (totalStrong a) (strongOver a)]; rfl
noncomputable def leftCone : lRoute e d r δ a ⋙ leafAt Z d ⟶ leafAt Y e ⋙ totalStrong a :=
  join (restrict Y e d r δ) (atEndpoint a d) (leafAt Z d) (leafAt Y d) (totalStrong a) (leafAt Y e) (leafAt Y e ⋙ totalStrong a)
    (actionLeaf d (totalStrong a) (strongOver a)) rfl (tip Y e d r δ)
noncomputable def rightCone : rRoute e d r δ a ⋙ leafAt Z d ⟶ leafAt Y e ⋙ totalStrong a :=
  pullCone (atEndpoint a e) (restrict Z e d r δ) (leafAt Z d) (leafAt Z e) (leafAt Y e ⋙ totalStrong a)
    (tip Z e d r δ) (actionLeaf e (totalStrong a) (strongOver a))
theorem leftAligned (x) : Aligned ((leftCone e d r δ a).app x) ((totalStrong a).map ((tip Y e d r δ).app x)) :=
  joinAligned (restrict Y e d r δ) (atEndpoint a d) (leafAt Z d) (leafAt Y d) (totalStrong a) (leafAt Y e) _ _ rfl (tip Y e d r δ) x
theorem rightAligned (x) : Aligned ((rightCone e d r δ a).app x) ((tip Z e d r δ).app ((atEndpoint a e).obj x)) := by
  simpa only [rightCone,pullCone,joinRight,NatTrans.comp_app,eqToHom_app,whiskerLeft_app] using
    Aligned.trailing ((tip Z e d r δ).app ((atEndpoint a e).obj x)) (Functor.congr_obj (actionLeaf e (totalStrong a) (strongOver a)) x)
theorem lCart (x) : Cartesian (proj Z) ((leftCone e d r δ a).app x) :=
  cartAligned (leftAligned e d r δ a x) (strongCart a _ (tipCart Y e d r δ x))
theorem rCart (x) : Cartesian (proj Z) ((rightCone e d r δ a).app x) :=
  cartAligned (rightAligned e d r δ a x) (tipCart Z e d r δ _)
theorem baseAlign (x) : Aligned ((proj Z).map ((leftCone e d r δ a).app x)) ((proj Z).map ((rightCone e d r δ a).app x)) := by
  apply ((leftAligned e d r δ a x).map (proj Z)).trans
  apply (NativeCube.functorAlign (strongOver a) ((tip Y e d r δ).app x)).trans
  apply (NativeCube.ofEq (tipBase Y e d r δ x)).trans
  apply (ContextadPayloadModification.appChange δ (Functor.congr_obj (actionGrade e (totalStrong a) (strongOver a)).symm x)).trans
  exact (NativeCube.ofEq (tipBase Z e d r δ _)).symm.trans ((rightAligned e d r δ a x).map (proj Z)).symm
abbrev sameBase := congrArg (· ⋙ d) (sameGrade e d r δ a)
theorem coneOver (x) : (proj Z).map ((leftCone e d r δ a).app x) = eqToHom (Functor.congr_obj (sameBase e d r δ a) x) ≫ (proj Z).map ((rightCone e d r δ a).app x) := by
  simpa using (baseAlign e d r δ a x).comm
noncomputable def payloadMate := compare (proj Z) (leftCone e d r δ a) (rightCone e d r δ a) (sameBase e d r δ a)
  (coneOver e d r δ a) (lCart e d r δ a) (rCart e d r δ a)
theorem mateBase (x) : Pure ((proj Z).map ((payloadMate e d r δ a).hom.app x)) :=
  ⟨_,factorOver (proj Z) _ _ (sameBase e d r δ a) (coneOver e d r δ a) (rCart e d r δ a) x⟩
noncomputable def weakSquare : lRoute e d r δ a ≅ rRoute e d r δ a :=
  mateIso Z d _ _ (sameGrade e d r δ a) (payloadMate e d r δ a) (mateBase e d r δ a)
theorem weakGrade (x) : Pure (gradeMap ((weakSquare e d r δ a).hom.app x)) :=
  mateGrade Z d _ _ (sameGrade e d r δ a) (payloadMate e d r δ a) (mateBase e d r δ a) x
end ContextualComposition.GrothendieckStep.ContextadWeakWeight
