module
public import ContextualComposition.ContextadNativeLaws
public import ContextualComposition.BlockCompositor
public import ContextualComposition.SuffixCell
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadWeakAction
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks BoundaryPaste
set_option backward.isDefEq.respectTransparency false
universe b w k l
variable {B : Type b} [Category.{w} B] {K : Type k} [Category.{l} K]
/- Pull an actual total functor over the endpoint projection back to a grade category.
The functor need not preserve the chosen lifts literally. -/
variable {Y Z W : Bᵒᵖ ⥤ Cat.{w,b}} (e : K ⥤ B)
variable (F : Total Y (𝟭 B) ⥤ Total Z (𝟭 B)) (h : F ⋙ pr Z = pr Y)
noncomputable def action : Total Y e ⥤ Total Z e :=
  view Y e ⋙ along e (pr Y) (pr Z) F h ⋙ unview Z e
theorem actionView : action e F h ⋙ view Z e = view Y e ⋙ along e (pr Y) (pr Z) F h :=
  (congrArg ((view Y e ⋙ along e (pr Y) (pr Z) F h) ⋙ ·) (unview_view Z e)).trans (Functor.comp_id _)
theorem actionGrade : action e F h ⋙ gradeProjection = gradeProjection :=
  congrArg (· ⋙ Strict.fst e (pr Z)) (actionView e F h)
theorem actionLeaf : action e F h ⋙ second (projectionData Z) e = second (projectionData Y) e ⋙ F :=
  congrArg (· ⋙ Strict.snd e (pr Z)) (actionView e F h)
theorem uniqueAction (J : Total Y e ⥤ Total Z e)
    (a : J ⋙ gradeProjection = gradeProjection)
    (b : J ⋙ second (projectionData Z) e = second (projectionData Y) e ⋙ F) : J = action e F h :=
  fold_ext e Z (a.trans (actionGrade e F h).symm) (b.trans (actionLeaf e F h).symm)
theorem actionIdentity : action (Y := Y) e (𝟭 _) rfl = 𝟭 _ :=
  (uniqueAction e (𝟭 _) rfl (𝟭 _) rfl rfl).symm
theorem actionComp (G : Total Z (𝟭 B) ⥤ Total W (𝟭 B)) (g : G ⋙ pr W = pr Z) :
    action e F h ⋙ action e G g = action e (F ⋙ G) ((congrArg (F ⋙ ·) g).trans h) :=
  uniqueAction _ _ _ _ ((congrArg (action e F h ⋙ ·) (actionGrade e G g)).trans (actionGrade e F h))
    ((congrArg (action e F h ⋙ ·) (actionLeaf e G g)).trans (congrArg (· ⋙ G) (actionLeaf e F h)))
theorem onStrict (t : Y ⟶ Z) : action e (ChainPayload.fibreMap t (𝟭 B)) rfl = ChainPayload.fibreMap t e :=
  (uniqueAction e _ rfl _ rfl rfl).symm
end ContextualComposition.GrothendieckStep.ContextadWeakAction

namespace ContextualComposition.GrothendieckStep.ContextadWeakAction
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks NativePacked BlockEvaluation
open ContextadRoutes ContextadLawTransport
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
universe u v
section General
variable {B I J K M : Type*} [Category* B] [Category* I] [Category* J] [Category* K] [Category* M]
variable (Y : Bᵒᵖ ⥤ Cat.{v,u})
theorem tailSquare (p : I ⥤ K) (q : J ⥤ M) (f : K ⥤ M) (g : I ⥤ J)
    (e : K ⥤ B) (d : M ⥤ B) (a : I ⥤ B) (b : J ⥤ B)
    (ha : p ⋙ e = a) (hb : q ⋙ d = b) (h : g ⋙ q = p ⋙ f) (l : f ⋙ d ⟶ e) :
    restrict Y a b g (eqToHom ((congrArg (g ⋙ ·) hb.symm).trans (congrArg (· ⋙ d) h)) ≫
      whiskerLeft p l ≫ eqToHom ha) ⋙ SpanPayload.totalMap Y q d hb =
    SpanPayload.totalMap Y p e ha ⋙ restrict Y e d f l := by
  subst a; subst b
  rw [ContextadVertical.strictWeight,ContextadVertical.strictWeight,← restrict_paste,← restrict_paste]
  apply restrict_congr _ _ _ h
  have w : whiskerLeft g (𝟙 (q ⋙ d)) = 𝟙 _ := by ext; simp
  simp only [pasteLift,eqToHom_refl,w,Category.comp_id]
  have strip {X X' Z : I ⥤ B} (h' : X = X') (m : X' ⟶ Z) :
      HEq (𝟙 X ≫ eqToHom h' ≫ m) m := by subst X'; simp
  exact strip (congrArg (· ⋙ d) h) (whiskerLeft p l)
end General
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (Y : PackedCuts.Psh.{u,max u v,u,v} B)
noncomputable abbrev splitAt (k i : Nat) := Lift.total (cut S (k,i)) Y ⋙ BlockEvaluation.suffix S Y k i
noncomputable abbrev frontAt (k i : Nat) := gradeProjection (Y := Y) (e := (power S (k+i)).dest) ⋙ (blocks S k i).first
noncomputable abbrev tailAt (k i : Nat) := SpanPayload.totalMap Y (blocks S k i).rest (power S i).dest (blocks S k i).dest
theorem splitFront (k i : Nat) : splitAt (S := S) Y k i ⋙ gradeProjection = frontAt (S := S) Y k i :=
  (congrArg (Lift.total (cut S (k,i)) Y ⋙ ·) (suffix_grade S Y k i)).trans
    (congrArg (· ⋙ Strict.fst _ _) (SpanPayload.total_projection Y _ _ (cut S (k,i)).dest))
theorem splitTail (k i : Nat) : splitAt (S := S) Y k i ⋙ NativeTrace.leaf (out S Y i) _ = tailAt (S := S) Y k i ⋙ BlockEvaluation.global S Y i :=
  (congrArg (Lift.total (cut S (k,i)) Y ⋙ ·) (suffix_boundary S Y k i)).trans
    (congrArg (· ⋙ BlockEvaluation.global S Y i) (SpanPayload.total_comp Y _ _ (cut S (k,i)).dest _ _ rfl))
theorem whiskFront (k : Nat) {i j} (r : Map S i j) :
    raw Y (inside k r) ⋙ frontAt (S := S) Y k j = frontAt (S := S) Y k i :=
  congrArg (gradeProjection ⋙ ·) ((blocks S k j).first_assemble ..)
theorem whiskTail (k : Nat) {i j} (r : Map S i j) :
    raw Y (inside k r) ⋙ tailAt Y k j = tailAt Y k i ⋙ raw Y r :=
  tailSquare Y _ _ _ _ _ _ _ _ (blocks S k i).dest (blocks S k j).dest ((blocks S k j).rest_assemble ..) r.leg

theorem splitInside (k : Nat) {i j} (r : Map S i j) :
    raw Y (inside k r) ⋙ splitAt Y k j =
      splitAt Y k i ⋙ action (power S k).dest (ContextadLawTransport.global Y r) (ContextadLawTransport.over Y r) := by
  apply BoundaryPaste.fold_ext
  · exact (congrArg (raw Y (inside k r) ⋙ ·) (splitFront (S := S) Y k j)).trans
      ((whiskFront Y k r).trans ((splitFront (S := S) Y k i).symm.trans
        (congrArg (splitAt Y k i ⋙ ·) (actionGrade _ _ _)).symm))
  · have erase : BlockEvaluation.global S Y i ⋙ ContextadLawTransport.global Y r =
        raw Y r ⋙ BlockEvaluation.global S Y j := ContextadRecognition.eraseInv _ _
    exact (congrArg (raw Y (inside k r) ⋙ ·) (splitTail (S := S) Y k j)).trans
      ((congrArg (· ⋙ BlockEvaluation.global S Y j) (whiskTail Y k r)).trans
      ((congrArg (tailAt Y k i ⋙ ·) erase.symm).trans
      ((congrArg (· ⋙ ContextadLawTransport.global Y r) (splitTail (S := S) Y k i).symm).trans
        (congrArg (splitAt (S := S) Y k i ⋙ ·) (actionLeaf (power S k).dest (ContextadLawTransport.global Y r) (ContextadLawTransport.over Y r))).symm)))
theorem unaryChange {G H : PackedCuts.Psh.{u,max u v,u,v} B} (A : B)
    (F : Total G (𝟭 B) ⥤ Total H (𝟭 B)) (h : F ⋙ BoundaryPaste.pr H = BoundaryPaste.pr G) :
    action (P.extend A) F h ⋙ ContextadVertical.insertOne (S := S) A H =
      ContextadVertical.insertOne (S := S) A G ⋙ action (power S 1).dest F h := by
  apply BoundaryPaste.fold_ext
  · exact (congrArg (action (P.extend A) F h ⋙ ·) (SpanPayload.total_projection H _ _ (ContextadChart.oneEnd S A))).trans
      ((congrArg (· ⋙ ContextadChart.one (P := P) A) (actionGrade _ F h)).trans
      ((SpanPayload.total_projection G _ _ (ContextadChart.oneEnd S A)).symm.trans
      (congrArg (ContextadVertical.insertOne (S := S) A G ⋙ ·) (actionGrade _ F h)).symm))
  · exact (congrArg (action (P.extend A) F h ⋙ ·) (NativeTrace.leaf_total H _ _ (ContextadChart.oneEnd S A))).trans
      ((actionLeaf _ F h).trans ((congrArg (· ⋙ F) (NativeTrace.leaf_total G _ _ (ContextadChart.oneEnd S A)).symm).trans
      (congrArg (ContextadVertical.insertOne (S := S) A G ⋙ ·) (actionLeaf _ F h)).symm))
end ContextualComposition.GrothendieckStep.ContextadWeakAction

