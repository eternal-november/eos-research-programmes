module
public import ContextualComposition.ContextadOuterStage
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
noncomputable def leftCore : (wr (S := S) Y r ⋙ last (S := S) Y V) ⟶ last (S := S) Y U :=
  gLift (S := S) Y r
noncomputable def rightCore : restrict (LY (S := S) Y) U.dest V.dest r.grade r.leg ⋙ NativeTrace.leaf (LY (S := S) Y) V.dest ⟶ NativeTrace.leaf (LY (S := S) Y) U.dest :=
  suffixRaw (P := projectionData (LY (S := S) Y)) (U := U) (V := V) r.grade r.leg
noncomputable def castNat {C D : Type*} [Category* C] [Category* D] {F G F' G' : C ⥤ D}
    (f : F' = F) (g : G = G') (a : F ⟶ G) : F' ⟶ G' := eqToHom f ≫ a ≫ eqToHom g
section Build
variable {C D E F G : Type*} [Category* C] [Category* D] [Category* E] [Category* F] [Category* G]
def join (r : C ⥤ D) (v : D ⥤ E) (l : E ⥤ F) (s : D ⥤ G) (k : G ⥤ F) (t : C ⥤ G) (u : C ⥤ F)
    (hv : v ⋙ l = s ⋙ k) (hu : t ⋙ k = u) (h : r ⋙ s ⟶ t) : (r ⋙ v) ⋙ l ⟶ u :=
  eqToHom (congrArg (r ⋙ ·) hv) ≫ whiskerRight h k ≫ eqToHom hu
def joinRight (r : C ⥤ D) (v : D ⥤ E) (l : E ⥤ F) (q : D ⥤ F) (a : v ⋙ l ⟶ q) :
    (r ⋙ v) ⋙ l ⟶ r ⋙ q := whiskerLeft r a
end Build
noncomputable def leftArrow : fstWay (S := S) Y r ⋙ NativeTrace.leaf (LY (S := S) Y) V.dest ⟶ prior (S := S) Y U :=
  join (wr (S := S) Y r) (stage (S := S) Y V) (NativeTrace.leaf (LY (S := S) Y) V.dest) (last (S := S) Y V) (BlockEvaluation.global S Y 1)
    (last (S := S) Y U) (prior (S := S) Y U) (stageLeaf (S := S) Y V) (stageLeaf (S := S) Y U).symm (leftCore (S := S) Y r)
noncomputable def rightArrow : sndWay (S := S) Y r ⋙ NativeTrace.leaf (LY (S := S) Y) V.dest ⟶ prior (S := S) Y U :=
  joinRight (stage (S := S) Y U) (restrict (LY (S := S) Y) U.dest V.dest r.grade r.leg)
    (NativeTrace.leaf (LY (S := S) Y) V.dest) (NativeTrace.leaf (LY (S := S) Y) U.dest) (rightCore (S := S) Y r)
end ContextualComposition.GrothendieckStep.ContextadOuterCharts
