module
public import ContextualComposition.NativePacked
@[expose] public section
namespace ContextualComposition.GrothendieckStep.BoundaryPaste
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks NativeCleavage
universe b w i j k l s t u v
variable {B : Type b} [Category.{w} B] {K : Type k} [Category.{l} K] {J : Type i} [Category.{j} J]
/-- Realize the category of elements of an ordinary payload as a strict
matching category. Only the projection is used; the auxiliary extension is constant. -/
def projectionData (Y : Bᵒᵖ ⥤ Cat.{w,b}) : Endpoints.{b,w,b,w} B where
  grades := Y
  extend a := (Functor.const _).obj a
  lift f := { app := fun _ => f }
variable (Y : Bᵒᵖ ⥤ Cat.{w,b}) (e : K ⥤ B) (p d : J ⥤ B)
abbrev pr (Y : Bᵒᵖ ⥤ Cat.{w,b}) := gradeProjection (Y := Y) (e := 𝟭 B)
abbrev view := strictFactor (projectionData Y) e
noncomputable abbrev unview := (view Y e).strictInv
theorem view_unview : view Y e ⋙ unview Y e = 𝟭 _ := (view Y e).asIsomorphism.unit_eq.symm
theorem unview_view : unview Y e ⋙ view Y e = 𝟭 _ := (view Y e).asIsomorphism.counit_eq
abbrev tail := SpanPayload.totalMap Y (Strict.snd e p) d rfl
abbrev front := gradeProjection (Y := Y) (e := Strict.snd e p ⋙ d) ⋙ Strict.fst e p
abbrev tailSource := gradeProjection (Y := Y) (e := d) ⋙ p
theorem boundary : front Y e p d ⋙ e = tail Y e p d ⋙ tailSource Y p d :=
  congrArg (gradeProjection ⋙ ·) (Strict.commute e p)
def separate := Strict.lift e (tailSource Y p d) (front Y e p d) (tail Y e p d) (boundary Y e p d)
abbrev fst := Strict.fst e (tailSource Y p d)
abbrev snd := Strict.snd e (tailSource Y p d)
def gradePair := Strict.lift e p (fst Y e p d) (snd Y e p d ⋙ gradeProjection) (Strict.commute e (tailSource Y p d))
noncomputable def assemble : Strict.Match e (tailSource Y p d) ⥤ Total Y (Strict.snd e p ⋙ d) :=
  attachLast (P := projectionData Y) _ (gradePair Y e p d) (snd Y e p d ⋙ second (projectionData Y) d) rfl
theorem assemble_grade : assemble Y e p d ⋙ gradeProjection = gradePair Y e p d := attach_prefix (P := projectionData Y) _ _ _ _
theorem assemble_leaf : assemble Y e p d ⋙ second (projectionData Y) _ = snd Y e p d ⋙ second (projectionData Y) d := attach_last (P := projectionData Y) _ _ _ _
theorem assemble_front : assemble Y e p d ⋙ front Y e p d = fst Y e p d :=
  congrArg (· ⋙ Strict.fst e p) (assemble_grade Y e p d)
theorem assemble_tail : assemble Y e p d ⋙ tail Y e p d = snd Y e p d := by
  apply last_ext (P := projectionData Y) d
  · exact congrArg (· ⋙ Strict.snd e p) (assemble_grade Y e p d)
  · exact assemble_leaf Y e p d
theorem assemble_separate : assemble Y e p d ⋙ separate Y e p d = 𝟭 _ :=
  Strict.uniq _ _ _ _ (assemble_front Y e p d) (assemble_tail Y e p d)
theorem separate_assemble : separate Y e p d ⋙ assemble Y e p d = 𝟭 _ := by
  apply last_ext (P := projectionData Y) _
  · apply (congrArg (separate Y e p d ⋙ ·) (assemble_grade Y e p d)).trans
    exact Strict.uniq _ _ _ _ rfl rfl
  · exact congrArg (separate Y e p d ⋙ ·) (assemble_leaf Y e p d)
noncomputable def separateIso : IsoCat (Total Y (Strict.snd e p ⋙ d)) (Strict.Match e (tailSource Y p d)) :=
  ⟨separate Y e p d,assemble Y e p d,(separate_assemble Y e p d).symm,assemble_separate Y e p d⟩
section Along
variable {L : Type s} [Category.{t} L] (q : L ⥤ B) (H : J ⥤ L) (over : H ⋙ q = p)
def along := Strict.lift e q (Strict.fst e p) (Strict.snd e p ⋙ H)
  ((Strict.commute e p).trans (congrArg (Strict.snd e p ⋙ ·) over.symm))
include over in
theorem invOver [H.IsIso] : H.strictInv ⋙ p = q :=
  (congrArg (H.strictInv ⋙ ·) over.symm).trans (congrArg (· ⋙ q) H.asIsomorphism.counit_eq)
noncomputable def alongIso [H.IsIso] : IsoCat (Strict.Match e p) (Strict.Match e q) where
  functor := along e p q H over
  inverse := along e q p H.strictInv (invOver p q H over)
  unit_eq := Strict.uniq _ _ _ _ rfl (congrArg (Strict.snd e p ⋙ ·) H.asIsomorphism.unit_eq)
  counit_eq := Strict.uniq _ _ _ _ rfl (congrArg (Strict.snd e q ⋙ ·) H.asIsomorphism.counit_eq)
end Along
section Fold
variable (G : Bᵒᵖ ⥤ Cat.{w,b}) (F : Total Y d ⥤ Total G (𝟭 B)) (h : F ⋙ pr G = tailSource Y p d)
/-- Evaluate just the suffix globally at the actual moving terminal boundary of the prefix. -/
noncomputable def fold := separate Y e p d ⋙ along e (tailSource Y p d) (pr G) F h ⋙ unview G e
theorem fold_view : fold Y e p d G F h ⋙ view G e = separate Y e p d ⋙ along e (tailSource Y p d) (pr G) F h :=
  (congrArg ((separate Y e p d ⋙ along e (tailSource Y p d) (pr G) F h) ⋙ ·) (unview_view G e)).trans (Functor.comp_id _)
theorem fold_grade : fold Y e p d G F h ⋙ gradeProjection = front Y e p d :=
  congrArg (· ⋙ Strict.fst e (pr G)) (fold_view Y e p d G F h)
theorem fold_suffix : fold Y e p d G F h ⋙ second (projectionData G) e = tail Y e p d ⋙ F :=
  congrArg (· ⋙ Strict.snd e (pr G)) (fold_view Y e p d G F h)
theorem fold_ext {X : Type*} [Category* X] {L M : X ⥤ Total G e}
    (a : L ⋙ gradeProjection = M ⋙ gradeProjection)
    (b : L ⋙ second (projectionData G) e = M ⋙ second (projectionData G) e) : L = M :=
  last_ext (P := projectionData G) e a b
noncomputable def foldIso [F.IsIso] : IsoCat (Total Y (Strict.snd e p ⋙ d)) (Total G e) :=
  ((separateIso Y e p d).trans (alongIso e _ _ F h)).trans (view G e).asIsomorphism.symm
theorem fold_iso_forward [F.IsIso] : (foldIso Y e p d G F h).functor = fold Y e p d G F h := rfl
end Fold
end ContextualComposition.GrothendieckStep.BoundaryPaste
