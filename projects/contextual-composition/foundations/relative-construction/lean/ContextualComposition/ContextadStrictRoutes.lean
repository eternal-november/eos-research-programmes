module
public import ContextualComposition.ContextadNativeLaws
public import ContextualComposition.ContextadCellPasting
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadStrictRoutes
open CategoryTheory CategoryTheory.Functor Opposite ContextadRoutes ContextadLawTransport ContextadNativeLaws
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable {i j : Nat} {r s : Map S i j}
/-- Literal coincidence of the two native grade functors and comparison
transformations, with dependent transport. It is strictly stronger than a cell. -/
structure Same (r s : Map S i j) : Prop where
  grade : r.grade = s.grade
  endpoint : HEq r.leg s.leg
theorem sameMap (h : Same r s) : r = s := by
  obtain ⟨r,hr,dr⟩ := r
  obtain ⟨s,hs,ds⟩ := s
  obtain ⟨e,k⟩ := h
  change r = s at e
  subst s
  cases eq_of_heq k
  rfl
variable (d : ContextadUnit.Data P) (m : ContextadTotal.Native S)
structure StrictData : Prop where
  left : Same (comp (leftUnit d) (tensor m)) (identity 1)
  right : Same (comp (rightUnit d) (tensor m)) (identity 1)
  assoc : Same (comp (firstTwo m) (tensor m)) (comp (lastTwo m) (tensor m))
variable (h : StrictData d m) (Y : PackedCuts.Psh.{u,max u v,u,v} B) (A : B)
include h
theorem left : evaluate Y (leftUnit d) A ⋙ ContextadCoherence.actual m Y A = 𝟭 _ :=
  (result m Y A _).trans ((congrArg (evaluate Y · A) (sameMap h.left)).trans (evalId Y 1 A))
theorem right : evaluate Y (rightUnit d) A ⋙ ContextadCoherence.actual m Y A = 𝟭 _ :=
  (result m Y A _).trans ((congrArg (evaluate Y · A) (sameMap h.right)).trans (evalId Y 1 A))
theorem assoc : evaluate Y (firstTwo m) A ⋙ ContextadCoherence.actual m Y A =
    evaluate Y (lastTwo m) A ⋙ ContextadCoherence.actual m Y A :=
  (result m Y A _).trans ((congrArg (evaluate Y · A) (sameMap h.assoc)).trans (result m Y A _).symm)
end ContextualComposition.GrothendieckStep.ContextadStrictRoutes
