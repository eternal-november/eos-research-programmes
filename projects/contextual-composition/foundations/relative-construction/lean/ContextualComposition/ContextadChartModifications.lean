module
public import ContextualComposition.ContextadStandardLaws
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadOuterCharts
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks NativeCleavage
open ContextadRoutes ContextadLawTransport ContextadNativeLaws ContextadModification FibreValue
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (d : ContextadUnit.Data P) (m : ContextadTotal.Native S) (Y : PackedCuts.Psh.{u,max u v,u,v} B)
theorem unitCart : gradeCart (insert S d) := by
  intro _ _ a _
  have : IsIso (payloadMap ((unitGrade d).map a)) := by change IsIso (eqToHom (d.reindex a).symm); infer_instance
  exact ContextadCartesian.cart_of_payload P.grades (𝟭 B) ((unitGrade d).map a)
theorem leftCartGrade : gradeCart (leftUnit (S := S) d) :=
  appendCart (insert S d) (nativeChoice 0) (unitCart d)
noncomputable def bridge {D : Type*} [Category* D] (G H : Dᵒᵖ ⥤ Cat) (F J : Total G (𝟭 D) ⥤ Total H (𝟭 D))
    (f : F ⋙ proj H = proj G) (j : J ⋙ proj H = proj G) (i : F ≅ J)
    (v : ∀ x, FibreValue.Pure ((proj H).map (i.hom.app x))) (p : Pres F (proj G) (proj H)) :=
  modification G H F J f j i v p (presIso i.symm p)
noncomputable def nativeBridge {i j : Nat} (r : Map S i j) (p : gradeCart r)
    (J : Total (PackedFree.pow S Y i) (𝟭 B) ⥤ Total (PackedFree.pow S Y j) (𝟭 B)) (h : J ⋙ proj _ = proj _)
    (a : global Y r ≅ J) (v : ∀ x, FibreValue.Pure ((proj (PackedFree.pow S Y j)).map (a.hom.app x))) :=
  bridge (PackedFree.pow S Y i) (PackedFree.pow S Y j) (global Y r) J (over Y r) h a v (globalPres Y r p)
noncomputable def outerUnitMod :=
  nativeBridge (i := 0+1) (j := 1+1) Y (suffix (insert S d)) (leftCartGrade (S := S) d) (global (LY (S := S) Y) (insert S d))
    (over (LY (S := S) Y) (insert S d)) (outerUnitTotal (S := S) Y d)  (fun x => outerUnitPure (S := S) Y d x)
noncomputable def outerTensorMod :=
  nativeBridge Y (firstTwo m) (firstCart m) (global (LY (S := S) Y) (tensor m))
    (over (LY (S := S) Y) (tensor m)) (outerTensorTotal Y m) (outerTensorPure Y m)
end ContextualComposition.GrothendieckStep.ContextadOuterCharts
