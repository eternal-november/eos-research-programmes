module
public import ContextualComposition.TripleBoundary
@[expose] public section
namespace ContextualComposition.GrothendieckStep.TripleEvaluation
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks NativeBlocks.Nested NativePacked BlockEvaluation WordTrace TripleBoundary
set_option backward.isDefEq.respectTransparency false
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split) (Y : Pr (B := B))
variable (n m k : Nat)
noncomputable abbrev collapseLast := lastPair (power S n) (power S m) (power S k) Y (out S Y k) (global S Y k) (globalOver S Y k)
noncomputable abbrev stagedLeft := collapseLast S Y n m k ⋙ totalStages S (out S Y k) n m
abbrev rebracket := Lift.total (regroup (power S n) (power S m) (power S k)) Y
noncomputable abbrev under (F : Total Y (fixed S (m,k)).dest ⥤ Total (out S (out S Y k) m) (𝟭 B))
    (h : F ⋙ gradeProjection = gradeProjection ⋙ (fixed S (m,k)).source) :=
  rebracket S Y n m k ⋙ BoundaryPaste.fold Y (power S n).dest (fixed S (m,k)).source (fixed S (m,k)).dest
    (out S (out S Y k) m) F h ⋙ global S (out S (out S Y k) m) n
noncomputable abbrev stagedRight := under S Y n m k (totalStages S Y m k) (totalOver S Y m k)
theorem stages : stagedLeft S Y n m k = stagedRight S Y n m k :=
  congrArg (· ⋙ global S (out S (out S Y k) m) n)
    (TripleBoundary.associativity (power S n) (power S m) (power S k) Y (out S Y k) (out S (out S Y k) m)
      (global S Y k) (globalOver S Y k) (global S (out S Y k) m) (globalOver S (out S Y k) m))
/-- Join exactly the indicated native blocks and retag their actual evaluator. -/
noncomputable abbrev grouped (i j : Nat) := Lift.total (BlockCompositor.join S i j) Y ⋙ global S Y (i+j) ⋙
  BlockCompositor.transport (PackedCuts.sameLength S Y (i,j)).symm
theorem groupedOver : grouped S Y m k ⋙ gradeProjection = gradeProjection ⋙ (fixed S (m,k)).source :=
  (congrArg (· ⋙ gradeProjection) (BlockCompositor.onMatched S Y m k).symm).trans (totalOver S Y m k)
noncomputable abbrev joinFirst := collapseLast S Y n m k ⋙ grouped S (out S Y k) n m
noncomputable abbrev joinLast := under S Y n m k (grouped S Y m k) (groupedOver S Y m k)
theorem underCongr {F G : Total Y (fixed S (m,k)).dest ⥤ Total (out S (out S Y k) m) (𝟭 B)}
    (h : F = G) {p : F ⋙ gradeProjection = gradeProjection ⋙ (fixed S (m,k)).source}
    {q : G ⋙ gradeProjection = gradeProjection ⋙ (fixed S (m,k)).source} :
    under S Y n m k F p = under S Y n m k G q := by subst G; rfl
theorem firstFace : stagedLeft S Y n m k = joinFirst S Y n m k :=
  congrArg (collapseLast S Y n m k ⋙ ·) (BlockCompositor.onMatched S (out S Y k) n m)
theorem lastFace : stagedRight S Y n m k = joinLast S Y n m k :=
  underCongr S Y n m k (BlockCompositor.onMatched S Y m k)
theorem fixedAssociativity : joinFirst S Y n m k = joinLast S Y n m k :=
  (firstFace S Y n m k).symm.trans ((stages S Y n m k).trans (lastFace S Y n m k))
end ContextualComposition.GrothendieckStep.TripleEvaluation
