module
public import ContextualComposition.TripleEvaluation
@[expose] public section
namespace ContextualComposition.GrothendieckStep.TripleTrace
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks NativeBlocks.Nested NativePacked BlockEvaluation WordTrace NativeTrace TripleBoundary TripleEvaluation
set_option backward.isDefEq.respectTransparency false
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split) (Y : Pr (B := B))
variable (n m k : Nat)
abbrev input := Total Y (L (power S n) (power S m) (power S k)).dest
abbrev output := Total (out S (out S (out S Y k) m) n) (𝟭 B)
def finish (t : Trace (P := P) (out S Y k)) : Trace (P := P) Y :=
  let r := read S Y k t.2
  (t.1 ++ r.1,r.2)
def observe (z : Edge (output S Y n m k)) := finish S Y k (flattenRead S (out S Y k) n m z)
abbrev first := gradeProjection (Y := Y) (e := (L (power S n) (power S m) (power S k)).dest) ⋙ a (power S n) (power S m) (power S k)
abbrev middle := gradeProjection (Y := Y) (e := (L (power S n) (power S m) (power S k)).dest) ⋙ b (power S n) (power S m) (power S k)
abbrev last := gradeProjection (Y := Y) (e := (L (power S n) (power S m) (power S k)).dest) ⋙ c (power S n) (power S m) (power S k)
abbrev terminal := NativeTrace.leaf Y (L (power S n) (power S m) (power S k)).dest
def expected (z : Edge (input S Y n m k)) : Trace (P := P) Y :=
  ((word S n (Edge.map (first S Y n m k) z) ++ word S m (Edge.map (middle S Y n m k) z)) ++ word S k (Edge.map (last S Y n m k) z),Edge.map (terminal S Y n m k) z)
theorem stageTrace (z : Edge (input S Y n m k)) :
    observe S Y n m k (Edge.map (stagedLeft S Y n m k) z) = expected S Y n m k z := by
  let U := power S n
  let V := power S m
  let W := power S k
  let G := out S Y k
  let F := global S Y k
  let C := collapseLast S Y n m k
  let T := SpanPayload.totalMap Y (c U V W) W.dest rfl
  have h := BlockCompositor.stagesTrace S G n m (Edge.map C z)
  have j := BoundaryPaste.fold_grade Y (product U V).dest W.source W.dest G F (globalOver S Y k)
  have j₁ := congrArg (fun H => word S n (Edge.map (H ⋙ Strict.fst U.dest V.source) z)) j
  have j₂ := congrArg (fun H => word S m (Edge.map (H ⋙ Strict.snd U.dest V.source) z)) j
  have b := congrArg (fun H => Edge.map H z) (BoundaryPaste.fold_suffix Y (product U V).dest W.source W.dest G F (globalOver S Y k))
  have p : flattenRead S G n m (Edge.map (stagedLeft S Y n m k) z) =
      (word S n (Edge.map (first S Y n m k) z) ++ word S m (Edge.map (middle S Y n m k) z),Edge.map F (Edge.map T z)) :=
    h.trans (Prod.ext (congrArg₂ List.append j₁ j₂) b)
  have u := read_global S Y k (Edge.map T z)
  have v := congrArg (fun H => word S k (Edge.map H z)) (SpanPayload.total_projection Y (c U V W) W.dest rfl)
  have w := congrArg (fun H => Edge.map H z) (NativeTrace.leaf_total Y (c U V W) W.dest rfl)
  have l : read S Y k (Edge.map F (Edge.map T z)) =
      (word S k (Edge.map (last S Y n m k) z),Edge.map (terminal S Y n m k) z) := u.trans (Prod.ext v w)
  unfold observe finish expected
  rw [p]
  change (_ ++ (read S Y k (Edge.map F (Edge.map T z))).1, (read S Y k (Edge.map F (Edge.map T z))).2) = _
  rw [l]
theorem groupedTrace (z : Edge (input S Y n m k)) :
    observe S Y n m k (Edge.map (joinLast S Y n m k) z) = expected S Y n m k z :=
  (congrArg (fun H => observe S Y n m k (Edge.map H z)) ((stages S Y n m k).trans (lastFace S Y n m k)).symm).trans
    (stageTrace S Y n m k z)
end ContextualComposition.GrothendieckStep.TripleTrace
