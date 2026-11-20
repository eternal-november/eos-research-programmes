module
public import ContextualComposition.AmbientRoutePaste
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientSerialBoundary
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite FibreValue TelescopeSquares
open ContextadAmbientPayload ContextadWeakWeight ContextadWeakAction SpanApex
open AmbientBicategory AmbientCoordinates AmbientHorizontalNaturality AmbientHorizontalFrames AmbientSquareBridge
open ContextadRoutes ContextadModification NativeBlocks CategoryTheory.Bicategory
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split)
variable {X Y : Obj.{u,v} B} {i j k : Nat} (r : Map S i j) (s : Map S j k) (p : gradeCart r) (q : gradeCart s) (pq : gradeCart (comp r s))
theorem serialFrame (X : Obj.{u,v} B) : oper S r p X ≫ oper S s q X = oper S (comp r s) pq X :=
  route S X r s pq q _ (totalOper S X r p).symm
variable (f : X ⟶ Y)
theorem serialAt (x) : Aligned (atRaw S (serial (comparison S r p f) (comparison S s q f)).inv x)
    ((AmbientComparisonRead.q S (comp r s) f).app x) := by
  have h₁ := (preAt S (oper S r p X) (comparison S s q f).inv x).trans
    ((AmbientComparisonRead.comparisonAt S s q f _).trans (ContextadPayloadModification.appChange _ (Functor.congr_obj (opEncode S r p X) x)))
  have h₂ := (postAt S (comparison S r p f).inv (oper S s q Y) x).trans
    ((NativeCube.functorAlign (opEncode S s q Y) _).trans ((AmbientComparisonRead.comparisonAt S r p f x).map _))
  simp only [serial,Iso.trans_inv,Iso.symm_inv,Strict.associator_eqToIso,eqToIso.inv,eqToIso.hom,compAt]
  exact (AmbientOperationLaws.trimFive _ _ _ _ _ (castAt S _ x) (castAt S _ x) (castAt S _ x) h₁ h₂).trans
    (AmbientRoutePaste.pasteMate _ _ _ r.grade s.grade r.leg s.leg f.hom x).symm
theorem bendAt {a b : obj S i X ⟶ obj S i Y} {l l₀ : obj S i X ⟶ obj S k X}
    {l' l₀' : obj S i Y ⟶ obj S k Y} (e : a = b) (h : l = l₀) (j : l' = l₀')
    (t : b ≫ l₀' ≅ l₀ ≫ AmbientBicategory.map S k f) (x) :
    Aligned (atRaw S (bend e h j t).inv x) (atRaw S t.inv x) := by
  subst b; subst l₀; subst l₀'; simp [bend,Aligned.refl]
theorem serialMate : serial (comparison S r p f) (comparison S s q f) =
    bend rfl (serialFrame S r s p q pq X) (serialFrame S r s p q pq Y) (comparison S (comp r s) pq f) := by
  apply Iso.ext_inv; apply extRaw S; intro x
  exact (serialAt S r s p q f x).trans
    (((bendAt S f _ _ _ _ x).trans (AmbientComparisonRead.comparisonAt S (comp r s) pq f x)).symm)
end ContextualComposition.GrothendieckStep.AmbientSerialBoundary
