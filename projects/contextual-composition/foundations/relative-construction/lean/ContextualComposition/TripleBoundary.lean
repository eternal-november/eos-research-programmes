module
public import ContextualComposition.EmptyUnitOverlap
@[expose] public section
namespace ContextualComposition.GrothendieckStep.TripleBoundary
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks NativeBlocks.Nested
set_option backward.isDefEq.respectTransparency false
universe u v
variable {B : Type u} [Category.{max u v} B] (U V W : Span (B := B))
abbrev L := product (product U V) W
abbrev R := product U (product V W)
abbrev ab := Strict.fst (product U V).dest W.source
abbrev a := ab U V W ⋙ Strict.fst U.dest V.source
abbrev b := ab U V W ⋙ Strict.snd U.dest V.source
abbrev c := Strict.snd (product U V).dest W.source
def bc := Strict.lift V.dest W.source (b U V W) (c U V W) (Strict.commute _ _)
def regroup : Over (L U V W) (R U V W) :=
  ⟨Strict.lift _ _ (a U V W) (bc U V W) (congrArg (ab U V W ⋙ ·) (Strict.commute U.dest V.source)),rfl,rfl⟩
variable (Y G H : Bᵒᵖ ⥤ Cat.{max u v,u})
variable (F : Total Y W.dest ⥤ Total G (𝟭 B)) (p : F ⋙ gradeProjection = gradeProjection ⋙ W.source)
variable (K : Total G V.dest ⥤ Total H (𝟭 B)) (q : K ⋙ gradeProjection = gradeProjection ⋙ V.source)
noncomputable abbrev lastPair := BoundaryPaste.fold Y (product U V).dest W.source W.dest G F p
noncomputable abbrev lastOne := BoundaryPaste.fold Y V.dest W.source W.dest G F p
noncomputable abbrev mid := BoundaryPaste.fold G U.dest V.source V.dest H K q
abbrev cutTail := SpanPayload.totalMap Y (bc U V W) (product V W).dest rfl
abbrev midPart := SpanPayload.totalMap G (Strict.snd U.dest V.source) V.dest rfl
theorem middleDiagram : lastPair U V W Y G F p ⋙ midPart U V G = cutTail U V W Y ⋙ lastOne V W Y G F p := by
  apply BoundaryPaste.fold_ext V.dest G
  · exact (congrArg (lastPair U V W Y G F p ⋙ ·) (SpanPayload.total_projection G (Strict.snd U.dest V.source) V.dest rfl)).trans
      ((congrArg (· ⋙ Strict.snd U.dest V.source) (BoundaryPaste.fold_grade Y (product U V).dest W.source W.dest G F p)).trans
      ((congrArg (· ⋙ Strict.fst V.dest W.source) (SpanPayload.total_projection Y (bc U V W) (product V W).dest rfl)).symm.trans
      (congrArg (cutTail U V W Y ⋙ ·) (BoundaryPaste.fold_grade Y V.dest W.source W.dest G F p)).symm))
  · exact (congrArg (lastPair U V W Y G F p ⋙ ·) (NativeTrace.leaf_total G (Strict.snd U.dest V.source) V.dest rfl)).trans
      ((BoundaryPaste.fold_suffix Y (product U V).dest W.source W.dest G F p).trans
      ((congrArg (· ⋙ F) (SpanPayload.total_comp Y (bc U V W) (product V W).dest rfl (Strict.snd V.dest W.source) W.dest rfl)).symm.trans
      (congrArg (cutTail U V W Y ⋙ ·) (BoundaryPaste.fold_suffix Y V.dest W.source W.dest G F p)).symm))
include q in
theorem tailOver : (lastOne V W Y G F p ⋙ K) ⋙ gradeProjection = gradeProjection ⋙ (product V W).source :=
  (congrArg (lastOne V W Y G F p ⋙ ·) q).trans (congrArg (· ⋙ V.source) (BoundaryPaste.fold_grade Y V.dest W.source W.dest G F p))
noncomputable abbrev pairLast := BoundaryPaste.fold Y U.dest (product V W).source (product V W).dest H
  (lastOne V W Y G F p ⋙ K) (tailOver V W Y G H F p K q)
set_option maxHeartbeats 1800000 in
theorem associativity :
    lastPair U V W Y G F p ⋙ mid U V G H K q =
      NativePacked.Lift.total (regroup U V W) Y ⋙ pairLast U V W Y G H F p K q := by
  apply BoundaryPaste.fold_ext U.dest H
  · exact (congrArg (lastPair U V W Y G F p ⋙ ·) (BoundaryPaste.fold_grade G U.dest V.source V.dest H K q)).trans
      ((congrArg (· ⋙ Strict.fst U.dest V.source) (BoundaryPaste.fold_grade Y (product U V).dest W.source W.dest G F p)).trans
      ((congrArg (· ⋙ Strict.fst U.dest (product V W).source) (SpanPayload.total_projection Y (regroup U V W).functor _ (regroup U V W).dest)).symm.trans
      (congrArg (NativePacked.Lift.total (regroup U V W) Y ⋙ ·) (BoundaryPaste.fold_grade Y U.dest (product V W).source (product V W).dest H (lastOne V W Y G F p ⋙ K) (tailOver V W Y G H F p K q))).symm))
  · exact (congrArg (lastPair U V W Y G F p ⋙ ·) (BoundaryPaste.fold_suffix G U.dest V.source V.dest H K q)).trans
      ((congrArg (· ⋙ K) (middleDiagram U V W Y G F p)).trans
      ((congrArg (· ⋙ lastOne V W Y G F p ⋙ K) (SpanPayload.total_comp Y (regroup U V W).functor _ (regroup U V W).dest (Strict.snd U.dest (product V W).source) _ rfl)).symm.trans
      (congrArg (NativePacked.Lift.total (regroup U V W) Y ⋙ ·) (BoundaryPaste.fold_suffix Y U.dest (product V W).source (product V W).dest H (lastOne V W Y G F p ⋙ K) (tailOver V W Y G H F p K q))).symm))
end ContextualComposition.GrothendieckStep.TripleBoundary
