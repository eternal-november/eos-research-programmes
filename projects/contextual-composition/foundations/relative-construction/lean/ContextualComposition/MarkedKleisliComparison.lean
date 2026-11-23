module
public import ContextualComposition.MarkedGenericFactorizations
public import ContextualComposition.RepresentablePurePins
public import ContextualComposition.ContentComposition

/-! Generic factorization of the actual coherent representable composition.
The identity-base reindexing is retained in the binary chart. -/

@[expose] public section
namespace ContextualComposition.GrothendieckStep.MarkedKleisliComparison
open CategoryTheory Opposite AmbientCoherentPseudomonad MarkedGenericFactorizations
universe u
set_option backward.isDefEq.respectTransparency false
variable {B : Type u} [Category.{u} B]

theorem context {P : Endpoints.{u,u,u,u} B} {S : P.Split} (T : Data S) (A : B)
    (p : P.grades.obj (op A)) (q : P.grades.obj (op ((P.extend A).obj p))) :
    let x := kappa A p
    let y := kappa ((P.extend A).obj p) q
    let z := SpanPayload.Power.gradeObj S 1 A (RepresentableCommaComposition.operand x y)
    let m := ContextadSpecialize.data T.mult
    (RepresentableCommaComposition.comp T).obj (x,y) = (CostructuredArrow.map
      ((m.delta A).app z ≫ (P.lift (𝟙 _)).app q)).obj (kappa A ((m.tensor A).obj z)) := by
  dsimp only
  rw [RepresentableCommaComposition.original]
  unfold RepresentableCommaComposition.exactNative
  refine CostructuredArrow.obj_ext _ _ ?_ ?_
  · rfl
  simp [kappa,RepresentableCommaComposition.operand]

open ContentCovariantGrothendieck ContentCovariantOperations

theorem content {P : Endpoints.{u,u,u,u} Bᵒᵖ} {S : P.Split} (T : Data S) (D : B)
    (q : (grades P).obj D) (p : (grades P).obj ((dest P D).obj q)) :
    let y := gamma D q
    let x := gamma ((dest P D).obj q) p
    let z := ContentComposition.chunk (S := S) x y
    (ContentComposition.nativeComp T).obj (x,y) =
      (StructuredArrow.map ((lift P (𝟙 _)).app p ≫ comparison T D z)).obj (gamma D (output T D z)) := by
  dsimp only
  rw [ContentComposition.nativeFormula]
  refine StructuredArrow.obj_ext _ _ ?_ ?_
  · rfl
  simp [gamma]

end ContextualComposition.GrothendieckStep.MarkedKleisliComparison
