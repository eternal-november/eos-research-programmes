module
public import ContextualComposition.ContextadOuterTips
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadOuterCharts
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks NativeCleavage BoundaryPaste
open ContextadRoutes ContextadWeakAction TelescopeSquares
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (Y : PackedCuts.Psh.{u,max u v,u,max u v} B)
variable {U V : Span (B := B)} (r : Operation U V)
theorem rightCart (x) : Cartesian (pr (LY (S := S) Y)) ((rightArrow (S := S) Y r).app x) :=
  cartesianLift _ _ _ _
theorem leftCart (x) : Cartesian (pr (LY (S := S) Y)) ((leftArrow (S := S) Y r).app x) := by
  simp only [leftArrow,join,NatTrans.comp_app,eqToHom_app,whiskerRight_app]
  apply pasteCart (ContextadCartesian.vertical_cart _)
  apply (pasteCart · (ContextadCartesian.vertical_cart _))
  apply (BlockCartesian.cartesian_iff (BlockEvaluation.global S Y 1) (BlockCartesian.isoIncoming _) _ _).mp
  rw [BlockEvaluation.globalOver]
  exact liftCart Y (right P S) (r₀ (P := P) r) (α (P := P) r) (left P)
    (fun z => cartesianLift P.grades (𝟭 B) ((second P U.dest).obj z) (r.leg.app (grade _ _ z))) x
end ContextualComposition.GrothendieckStep.ContextadOuterCharts

namespace ContextualComposition.GrothendieckStep.ContextadOuterCharts
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks NativeCleavage BoundaryPaste
open ContextadRoutes ContextadWeakAction TelescopeSquares
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
universe u v
section Cast
variable {C D : Type*} [Category* C] [Category* D] {F G H J : C ⥤ D}
theorem castApp (f : F = G) (g : H = J) (a : G ⟶ H) (x : C) :
    Aligned ((eqToHom f ≫ a ≫ eqToHom g).app x) (a.app x) := by
  subst G; subst J; simpa using Aligned.refl (a.app x)
theorem joinAligned {A₀ A₁ A₂ A₃ A₄ : Type*} [Category* A₀] [Category* A₁] [Category* A₂] [Category* A₃] [Category* A₄]
    (r : A₀ ⥤ A₁) (v : A₁ ⥤ A₂) (l : A₂ ⥤ A₃) (s : A₁ ⥤ A₄) (k : A₄ ⥤ A₃) (t : A₀ ⥤ A₄) (u : A₀ ⥤ A₃)
    (hv : v ⋙ l = s ⋙ k) (hu : t ⋙ k = u) (h : r ⋙ s ⟶ t) (x : A₀) :
    Aligned ((join r v l s k t u hv hu h).app x) (k.map (h.app x)) :=
  castApp (congrArg (r ⋙ ·) hv) hu (whiskerRight h k) x
end Cast
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (Y : PackedCuts.Psh.{u,max u v,u,v} B) {U V : Span (B := B)} (r : Operation U V)
theorem baseAligned (x) : Aligned ((pr (LY (S := S) Y)).map ((leftArrow (S := S) Y r).app x))
    ((pr (LY (S := S) Y)).map ((rightArrow (S := S) Y r).app x)) := by
  have a := (joinAligned (wr (S := S) Y r) (stage (S := S) Y V) (NativeTrace.leaf (LY (S := S) Y) V.dest)
    (last (S := S) Y V) (BlockEvaluation.global S Y 1) (last (S := S) Y U) (prior (S := S) Y U)
    (stageLeaf (S := S) Y V) (stageLeaf (S := S) Y U).symm (leftCore (S := S) Y r) x).map (pr (LY (S := S) Y))
  have b := NativeCube.functorAlign (BlockEvaluation.globalOver S Y 1) ((gLift (S := S) Y r).app x)
  have c := ContextadPayloadModification.appChange r.leg (Functor.congr_obj (stageHead (S := S) Y U).symm x)
  exact a.trans (b.trans c)
theorem outOver (x) : (pr (LY (S := S) Y)).map ((leftArrow (S := S) Y r).app x) =
    eqToHom (Functor.congr_obj (congrArg (· ⋙ V.dest) (gradeEq (S := S) Y r)) x) ≫
      (pr (LY (S := S) Y)).map ((rightArrow (S := S) Y r).app x) := by
  simpa using (baseAligned (S := S) Y r x).comm
noncomputable def stageComparison : fstWay (S := S) Y r ≅ sndWay (S := S) Y r :=
  let h := congrArg (· ⋙ V.dest) (gradeEq (S := S) Y r)
  let i := compare (pr (LY (S := S) Y)) (leftArrow (S := S) Y r) (rightArrow (S := S) Y r) h
    (outOver (S := S) Y r) (leftCart (S := S) Y r) (rightCart (S := S) Y r)
  mateIso (LY (S := S) Y) V.dest _ _ (gradeEq (S := S) Y r) i
    (fun x => ⟨_,factorOver (pr (LY (S := S) Y)) (leftArrow (S := S) Y r) (rightArrow (S := S) Y r) h (outOver (S := S) Y r) (rightCart (S := S) Y r) x⟩)
theorem stageVertical (x) : FibreValue.Pure (gradeMap ((stageComparison (S := S) Y r).hom.app x)) := by
  unfold stageComparison
  apply mateGrade
end ContextualComposition.GrothendieckStep.ContextadOuterCharts
