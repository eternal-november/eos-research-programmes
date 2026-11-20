module
public import ContextualComposition.AmbientSerialBoundary
public import ContextualComposition.AmbientDeepIndices
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientBoundaryReduction
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite FibreValue TelescopeSquares
open ContextadAmbientPayload ContextadWeakWeight ContextadWeakAction SpanApex
open AmbientBicategory AmbientCoordinates AmbientHorizontalNaturality AmbientHorizontalFrames AmbientSquareBridge
open ContextadRoutes ContextadModification NativeBlocks CategoryTheory.Bicategory
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
universe u v
set_option maxHeartbeats 1200000
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split)
variable {X Y : Obj.{u,v} B} {i j k : Nat} (f : X ⟶ Y)
open AmbientHorizontalDiagrams ContextadLawTransport ContextadNativeLaws ContextadOuterCharts
abbrev RRead {a b : obj S i X ⟶ obj S j Y} (z : a ≅ b) (r : Map S i j) : Prop :=
  ∀ x, Aligned (atRaw S z.inv x) ((AmbientComparisonRead.q S r f).app x)
theorem serialRaw {a : obj S i X ⟶ obj S i Y} {b : obj S j X ⟶ obj S j Y} {c : obj S k X ⟶ obj S k Y}
    {p : obj S i X ⟶ obj S j X} {p' : obj S i Y ⟶ obj S j Y} {q : obj S j X ⟶ obj S k X} {q' : obj S j Y ⟶ obj S k Y}
    (u : a ≫ p' ≅ p ≫ b) (v : b ≫ q' ≅ q ≫ c) (r : Map S i j) (s : Map S j k)
    (hu : RRead S f u r) (hv : RRead S f v s) (hx : encode S p = raw X r) (hy : encode S q' = raw Y s) :
    RRead S f (serial u v) (comp r s) := by
  intro x
  have h₁ := (preAt S p v.inv x).trans ((hv _).trans (ContextadPayloadModification.appChange _ (Functor.congr_obj hx x)))
  have h₂ := (postAt S u.inv q' x).trans ((NativeCube.functorAlign hy _).trans ((hu x).map _))
  simp only [serial,Iso.trans_inv,Iso.symm_inv,Strict.associator_eqToIso,eqToIso.inv,eqToIso.hom,compAt]
  exact (AmbientOperationLaws.trimFive _ _ _ _ _ (castAt S _ x) (castAt S _ x) (castAt S _ x) h₁ h₂).trans
    (AmbientRoutePaste.pasteMate _ _ _ r.grade s.grade r.leg s.leg f.hom x).symm
theorem toBend {a : obj S i X ⟶ obj S i Y} {u : obj S i X ⟶ obj S j X} {v : obj S i Y ⟶ obj S j Y}
    (e : a = AmbientBicategory.map S i f) (r : Map S i j) (p : gradeCart r)
    (l : u = oper S r p X) (h : v = oper S r p Y) (t : a ≫ v ≅ u ≫ AmbientBicategory.map S j f)
    (z : RRead S f t r) : t = bend e l h (comparison S r p f) := by
  apply Iso.ext_inv; apply extRaw S; intro x
  exact (z x).trans (((AmbientSerialBoundary.bendAt S f e l h _ x).trans (AmbientComparisonRead.comparisonAt S r p f x)).symm)
theorem castTarget {C : Type*} [Bicategory C] [Strict C] {x y : C} {p : x ⟶ x} {q : y ⟶ y} (a : x ⟶ y)
    (l : 𝟙 x = p) (r : 𝟙 y = q) (s : a ≫ q ≅ p ≫ a) (e : a ≫ q = p ≫ a) (w : s = eqToIso e) :
    AmbientHorizontalNaturality.identity a = bend rfl l r s := by
  subst p; subst q; subst s; ext
  simp [AmbientHorizontalNaturality.identity,bend,Strict.leftUnitor_eqToIso,Strict.rightUnitor_eqToIso]
set_option linter.defProp false in
def idTarget (i : Nat) := castTarget (AmbientBicategory.map S i f)
  (idRoute S X i).symm (idRoute S Y i).symm _ _ (AmbientIdentityOperation.comparison S i f)
variable (d : ContextadUnit.Data P) (m : ContextadTotal.Native S) (C : Constraints d m)
theorem muRead : RRead S f (squareM S m f) (tensor m) := by
  intro x
  simp only [squareM,Iso.trans_inv,eqToIso.inv,compAt]
  obtain ⟨e,w⟩ := castAt (X := X) (Y := Y) (i := 2) (j := 1) S (congrArg (· ≫ M S Y m) (twice S f)).symm x
  rw [w]
  exact (Aligned.trailing _ e).trans (AmbientComparisonRead.comparisonAt S (tensor m) m.cart f x)
end ContextualComposition.GrothendieckStep.AmbientBoundaryReduction
