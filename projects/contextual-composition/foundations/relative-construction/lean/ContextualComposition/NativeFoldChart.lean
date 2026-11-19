module
public import ContextualComposition.TaggedSquareRecognition
@[expose] public section
namespace ContextualComposition.GrothendieckStep.NativeFoldChart
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks NativeBlocks.Nested NativePacked BoundaryPaste
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000
variable {B : Type u} [Category.{max u v} B] (Y : WordTrace.Pr (B := B))
variable {U V U' V' : Span (B := B)} (a : Over U U') (b : Over V V')
abbrev pairTag := Lift.total (NativeAssoc.Three.mapProduct a b) Y
abbrev frontOf (U V : Span (B := B)) := front Y U.dest V.source V.dest
abbrev tailOf (U V : Span (B := B)) := tail Y U.dest V.source V.dest
theorem frontMap : pairTag Y a b ⋙ frontOf Y U' V' = frontOf Y U V ⋙ a.functor :=
  congrArg (· ⋙ Strict.fst U'.dest V'.source) (SpanPayload.total_projection Y (NativeAssoc.Three.mapProduct a b).functor _ (NativeAssoc.Three.mapProduct a b).dest)
theorem tailMap : pairTag Y a b ⋙ tailOf Y U' V' = tailOf Y U V ⋙ Lift.total b Y := by
  exact (SpanPayload.total_comp Y (NativeAssoc.Three.mapProduct a b).functor _ (NativeAssoc.Three.mapProduct a b).dest (Strict.snd U'.dest V'.source) _ rfl).trans
    (SpanPayload.total_comp Y (Strict.snd U.dest V.source) _ rfl b.functor _ b.dest).symm
variable {G H : WordTrace.Pr (B := B)} (t : G ⟶ H)
variable (F : Total Y V.dest ⥤ Total G (𝟭 B)) (K : Total Y V'.dest ⥤ Total H (𝟭 B))
variable (f : F ⋙ pr G = tailSource Y V.source V.dest) (k : K ⋙ pr H = tailSource Y V'.source V'.dest)
noncomputable abbrev foldAt (U V : Span (B := B)) {G : WordTrace.Pr (B := B)} (F : Total Y V.dest ⥤ Total G (𝟭 B)) (h : F ⋙ pr G = tailSource Y V.source V.dest) :=
  fold Y U.dest V.source V.dest G F h
theorem restriction (cut : Lift.total b Y ⋙ K = F ⋙ ChainPayload.fibreMap t (𝟭 B)) :
    pairTag Y a b ⋙ foldAt Y U' V' K k = foldAt Y U V F f ⋙ ChainPayload.fibreMap t U.dest ⋙ Lift.total a H := by
  apply fold_ext U'.dest H
  · calc
      _ = pairTag Y a b ⋙ frontOf Y U' V' := congrArg (pairTag Y a b ⋙ ·) (fold_grade ..)
      _ = frontOf Y U V ⋙ a.functor := frontMap Y a b
      _ = _ := (congrArg (· ⋙ a.functor) (fold_grade Y U.dest V.source V.dest G F f)).symm.trans
        (congrArg (fun z => foldAt Y U V F f ⋙ ChainPayload.fibreMap t U.dest ⋙ z) (SpanPayload.total_projection H a.functor _ a.dest)).symm
  · calc
      _ = pairTag Y a b ⋙ tailOf Y U' V' ⋙ K := congrArg (pairTag Y a b ⋙ ·) (fold_suffix ..)
      _ = tailOf Y U V ⋙ F ⋙ ChainPayload.fibreMap t (𝟭 B) := by rw [← Functor.assoc,tailMap,Functor.assoc,cut]
      _ = _ := (congrArg (· ⋙ ChainPayload.fibreMap t (𝟭 B)) (fold_suffix Y U.dest V.source V.dest G F f)).symm.trans
        ((congrArg (foldAt Y U V F f ⋙ ·) (CutFold.leafMap t U.dest)).symm.trans
        (congrArg (fun z => foldAt Y U V F f ⋙ ChainPayload.fibreMap t U.dest ⋙ z) (NativeTrace.leaf_total H a.functor _ a.dest)).symm)
end ContextualComposition.GrothendieckStep.NativeFoldChart
