module
public import ContextualComposition.ContextadPentagonSchedule
public import ContextualComposition.ContextadScheduleDetection
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadSchedule
open CategoryTheory CategoryTheory.Functor Opposite NativeBlocks SpanApex ContextadRoutes ContextadLawTransport ContextadNativeLaws ContextadHorizontalLaws ContextadScheduleDetection
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (d : ContextadUnit.Data P) (m : ContextadTotal.Native S) (c : Constraints d m)
abbrev EvaluatedLaws (Y : PackedCuts.Psh.{u,max u v,u,v} B) (A : B) : Prop :=
  paste Y A (triLong d m c (canonicalTriangle d m c)) = paste Y A (triShort d m c) ∧
  paste Y A (pentLong d m c (canonicalPentagon d m c)) = paste Y A (pentShort d m c (canonicalPentagon d m c))
theorem coherentObserver : Coherent d m c ↔ ∀ A, EvaluatedLaws d m c (observer B) A := by
  constructor
  · exact fun h A => ⟨triangleAt d m c h.triangle _ A,pentagonAt d m c h.pentagon _ A⟩
  · exact fun h => ⟨(pathIff _ _).mpr (fun A => (h A).1),(pathIff _ _).mpr (fun A => (h A).2)⟩
theorem coherentAll : Coherent d m c ↔ ∀ (Y : PackedCuts.Psh.{u,max u v,u,v} B) (A : B), EvaluatedLaws d m c Y A := by
  constructor
  · exact fun h Y A => ⟨triangleAt d m c h.triangle Y A,pentagonAt d m c h.pentagon Y A⟩
  · exact fun h => (coherentObserver d m c).mpr (h (observer B))
end ContextualComposition.GrothendieckStep.ContextadSchedule
