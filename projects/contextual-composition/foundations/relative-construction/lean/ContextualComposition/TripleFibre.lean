module
public import ContextualComposition.TripleTrace
@[expose] public section
namespace ContextualComposition.GrothendieckStep.TripleFibre
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks NativeBlocks.Nested NativePacked BlockEvaluation WordTrace TripleBoundary TripleEvaluation
set_option backward.isDefEq.respectTransparency false
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split) (Y : Pr (B := B))
variable (n m k : Nat)
abbrev triple := L (power S n) (power S m) (power S k)
abbrev family := out S (out S (out S Y k) m) n
abbrev src := NativeCleavage.FibreTotal.projection Y (triple S n m k).dest (triple S n m k).source
theorem stageOver : stagedLeft S Y n m k ⋙ gradeProjection = src S Y n m k :=
  (congrArg (collapseLast S Y n m k ⋙ ·) (totalOver S (out S Y k) n m)).trans
    (congrArg (· ⋙ (fixed S (n,m)).source)
      (BoundaryPaste.fold_grade Y (fixed S (n,m)).dest (power S k).source (power S k).dest (out S Y k) (global S Y k) (globalOver S Y k)))
theorem firstOver : joinFirst S Y n m k ⋙ gradeProjection = src S Y n m k :=
  (congrArg (· ⋙ gradeProjection) (firstFace S Y n m k).symm).trans (stageOver S Y n m k)
theorem lastOver : joinLast S Y n m k ⋙ gradeProjection = src S Y n m k :=
  (congrArg (· ⋙ gradeProjection) (fixedAssociativity S Y n m k).symm).trans (firstOver S Y n m k)
theorem stageIso : (stagedLeft S Y n m k).IsIso := by
  let F := collapseLast S Y n m k
  let _ : F.IsIso := (BoundaryPaste.foldIso Y (fixed S (n,m)).dest (power S k).source (power S k).dest (out S Y k) (global S Y k) (globalOver S Y k)).isIso_functor
  let _ := totalIso S (out S Y k) n m
  exact (F.asIsomorphism.trans (totalStages S (out S Y k) n m).asIsomorphism).isIso_functor
theorem lastIso : (joinLast S Y n m k).IsIso :=
  ((stages S Y n m k).trans (lastFace S Y n m k)) ▸ stageIso S Y n m k
variable (A : B)
noncomputable abbrev valueOf (F : TripleTrace.input S Y n m k ⥤ TripleTrace.output S Y n m k)
    (h : F ⋙ gradeProjection = src S Y n m k) :=
  NativeCleavage.FibreTotal.into Y (triple S n m k).dest (triple S n m k).source A ⋙
    SpanPayload.fibreFunctor F _ h A ⋙ FibreValue.value (family S Y n m k) A
theorem valueCongr {F G : TripleTrace.input S Y n m k ⥤ TripleTrace.output S Y n m k}
    (h : F = G) {p : F ⋙ gradeProjection = src S Y n m k} {q : G ⋙ gradeProjection = src S Y n m k} :
    valueOf S Y n m k A F p = valueOf S Y n m k A G q := by subst G; rfl
theorem atOuter : valueOf S Y n m k A (joinFirst S Y n m k) (firstOver S Y n m k) =
    valueOf S Y n m k A (joinLast S Y n m k) (lastOver S Y n m k) := valueCongr S Y n m k A (fixedAssociativity S Y n m k)
end ContextualComposition.GrothendieckStep.TripleFibre
