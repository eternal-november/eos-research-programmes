module
public import ContextualComposition.ContextadAmbientLift
public import ContextualComposition.PackedFree

@[expose] public section
namespace ContextualComposition.GrothendieckStep.TelescopeGradeChange
open CategoryTheory CategoryTheory.Functor Opposite
open SpanApex BoundaryPaste ContextadWeakAction ContextadAmbientPayload
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans

set_option backward.isDefEq.respectTransparency false
universe b w k j l i
variable {B : Type b} [Category.{w} B] {K : Type k} [Category.{j} K] {L : Type l} [Category.{i} L]
variable {Y Z : Bᵒᵖ ⥤ Cat.{w,b}} (a : Pseudofunctor.StrongTrans Y.toPseudofunctor' Z.toPseudofunctor')
variable (r : K ⥤ L) (d : L ⥤ B) {e : K ⥤ B} (h : r ⋙ d = e)

/-- A grade presentation map over the endpoint preserves the complete terminal payload arrow. -/
theorem totalMap_leaf (X : Bᵒᵖ ⥤ Cat.{w,b}) :
    SpanPayload.totalMap X r d h ⋙ second (projectionData X) d = second (projectionData X) e := by
  subst e
  rfl

/-- Strong payload change commutes with a grade functor over the same endpoint. -/
theorem totalMap_payload :
    SpanPayload.totalMap Y r d h ⋙ atEndpoint a d = atEndpoint a e ⋙ SpanPayload.totalMap Z r d h := by
  apply fold_ext d Z
  · exact (congrArg (SpanPayload.totalMap Y r d h ⋙ ·) (actionGrade d (totalStrong a) (strongOver a))).trans
      ((SpanPayload.total_projection Y r d h).trans
        ((congrArg (· ⋙ r) (actionGrade e (totalStrong a) (strongOver a))).symm.trans
          (congrArg (atEndpoint a e ⋙ ·) (SpanPayload.total_projection Z r d h)).symm))
  · exact (congrArg (SpanPayload.totalMap Y r d h ⋙ ·) (actionLeaf d (totalStrong a) (strongOver a))).trans
      ((congrArg (· ⋙ totalStrong a) (totalMap_leaf r d h Y)).trans
        ((actionLeaf e (totalStrong a) (strongOver a)).symm.trans
          (congrArg (atEndpoint a e ⋙ ·) (totalMap_leaf r d h Z)).symm))

section Coproduct

open CoproductSpan
universe t v u
variable {I : Type t} {C : I → Type u} [∀ n, Category.{v} (C n)]
variable (legs : ∀ n, C n ⥤ B)

/-- The same covariance holds after assembling all tags of a coproduct. -/
theorem gather_payload :
    Distribute.gather Y legs ⋙ atEndpoint a (Sigma.desc legs) =
      ZeroPower.Sum.map (fun n => atEndpoint a (legs n)) ⋙ Distribute.gather Z legs := by
  apply PackedFree.sigma_ext
  intro n
  exact totalMap_payload a (Sigma.incl n) (Sigma.desc legs) (e := legs n) rfl

variable (src dst : ∀ n, C n ⥤ B) (A : B)

/-- The actual tagged comparison into the weighted whole span commutes with strong payload maps. -/
theorem compare_payload :
    compare src dst A Y ⋙ atEndpoint a (wholeLeg src dst A) =
      ZeroPower.Sum.map (fun n => atEndpoint a (leg src dst A n)) ⋙ compare src dst A Z := by
  exact (EvalPayload.pasteEq _ _ _ _ _ _ _ (gather_payload a (leg src dst A)).symm
    (totalMap_payload a (pack src A) (wholeLeg src dst A) (over src dst A)).symm).symm

end Coproduct

section Lengths

open CoproductSpan CoproductSpan.All
variable {Q : Endpoints.{b,w,b,w} B} (R : Q.Split) (A : B)

/-- Move the known strong square across the inverse of the actual single-span comparison. -/
noncomputable def inverse_payload :=
  SumChange.inverseSquare (compare (src R) (dst R) A Y).asEquivalence
    (compare (src R) (dst R) A Z).asEquivalence
    (eqToIso (compare_payload a (src R) (dst R) A))

/-- Lengthwise comparison squares assemble into the square of the original telescope evaluation. -/
noncomputable def evaluation_of_components
    (targets : ∀ n, (Iterates.layer Q R Y n).obj (op A) ⥤ (Iterates.layer Q R Z n).obj (op A))
    (cells : ∀ n, (component R Y A n).functor ⋙ targets n ≅
      atEndpoint a (leg (src R) (dst R) A n) ⋙ (component R Z A n).functor) :
    (evaluation R Y A).functor ⋙ ZeroPower.Sum.map targets ≅
      atEndpoint a (wholeLeg (src R) (dst R) A) ⋙ (evaluation R Z A).functor :=
  SpanPayload.pasteIso (inverse_payload a R A)
    (SumChange.Tagged.square (fun n => (component R Y A n).functor) (fun n => (component R Z A n).functor)
      (fun n => atEndpoint a (leg (src R) (dst R) A n)) targets cells)

end Lengths

end ContextualComposition.GrothendieckStep.TelescopeGradeChange
