module
public import ContextualComposition.AmbientIdentityOperation
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientRoutePaste
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite FibreValue TelescopeSquares
open ContextadAmbientPayload ContextadWeakWeight ContextadWeakAction AmbientMateCalculus SpanApex
open scoped CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
universe u v
variable {B K L M : Type u} [Category.{v} B] [Category.{v} K] [Category.{v} L] [Category.{v} M]
variable (e : K ⥤ B) (d : L ⥤ B) (c : M ⥤ B) (r : K ⥤ L) (s : L ⥤ M) (l : r ⋙ d ⟶ e) (m : s ⋙ c ⟶ d)
variable (Y : Bᵒᵖ ⥤ Cat.{v,u})
theorem tipPaste (x : Total Y e) :
    Aligned ((tip Y e c (r ⋙ s) (pasteLift e d c r s l m)).app x)
      ((tip Y d c s m).app ((restrict Y e d r l).obj x) ≫ (tip Y e d r l).app x) := by
  apply ContextadUnitTotal.pureAlign Y (𝟭 B)
  · exact congrArg (leafAt Y c).obj (Functor.congr_obj (restrict_paste Y e d c r s l m) x)
  · rfl
  · exact Aligned.refl _
  · exact pureId _
  · exact WeightedCells.totalPureComp _ _ (pureId _) (pureId _)
variable {Y} {Z : Bᵒᵖ ⥤ Cat.{v,u}} (a : StrongTrans Y.toPseudofunctor' Z.toPseudofunctor')
noncomputable abbrev stages (x : Total Y e) :=
  (q d c s m a).app ((restrict Y e d r l).obj x) ≫ (restrict Z d c s m).map ((q e d r l a).app x)
theorem stageFactor (x : Total Y e) :
    Aligned ((leafAt Z c).map (stages e d c r s l m a x) ≫
      ((tip Z d c s m).app ((restrict Z e d r l).obj ((atEndpoint a e).obj x)) ≫ (tip Z e d r l).app ((atEndpoint a e).obj x)))
      ((totalStrong a).map ((tip Y e c (r ⋙ s) (pasteLift e d c r s l m)).app x)) := by
  let h := (q e d r l a).app x
  let k := (q d c s m a).app ((restrict Y e d r l).obj x)
  let j := leafAt Z c
  let b := (atEndpoint a e).obj x
  change Aligned (j.map (k ≫ (restrict Z d c s m).map h) ≫ _) _
  have nat : j.map ((restrict Z d c s m).map h) ≫ (tip Z d c s m).app ((restrict Z e d r l).obj b) = (tip Z d c s m).app ((atEndpoint a d).obj ((restrict Y e d r l).obj x)) ≫ (leafAt Z d).map h := (tip Z d c s m).naturality h
  rw [Functor.map_comp,Category.assoc,← Category.assoc ((j.map ((restrict Z d c s m).map h))), nat,Category.assoc,← Category.assoc]
  apply ((factor d c s m a ((restrict Y e d r l).obj x)).comp (factor e d r l a x)).trans
  exact (NativeCube.ofEq ((totalStrong a).map_comp _ _).symm).trans ((tipPaste e d c r s l m Y x).map _).symm
theorem pasteMate (x : Total Y e) :
    Aligned ((q e c (r ⋙ s) (pasteLift e d c r s l m) a).app x) (stages e d c r s l m a x) := by
  let b := (atEndpoint a e).obj x
  let F := atEndpoint a c
  let R := restrict Z e c (r ⋙ s) (pasteLift e d c r s l m)
  let J := leafAt Z c
  let j := stages e d c r s l m a x
  let hx := congrArg F.obj (Functor.congr_obj (restrict_paste Y e d c r s l m) x)
  let hy := Functor.congr_obj (restrict_paste Z e d c r s l m) b
  let v := eqToHom hx ≫ j ≫ eqToHom hy.symm
  have tr : Aligned v j := AmbientDescentRecognition.trim _ _ _ ⟨_,rfl⟩ ⟨_,rfl⟩
  have gr : Pure (gradeMap j) := by
    change Pure (gradeMap (_ ≫ _))
    rw [grade_comp]
    exact pureComp (weakGrade d c s m a _) (pureMap s (weakGrade e d r l a x))
  have h : (q e c (r ⋙ s) (pasteLift e d c r s l m) a).app x = v := by
    apply cancelTip e c (r ⋙ s) (pasteLift e d c r s l m) b _ _ (weakGrade _ _ _ _ _ x) (pureOfAligned (tr.map gradeProjection) gr)
    apply (factor e c (r ⋙ s) (pasteLift e d c r s l m) a x).trans
    exact (((tr.map J).comp (tipPaste e d c r s l m Z b)).trans (stageFactor e d c r s l m a x)).symm
  exact (NativeCube.ofEq h).trans tr
end ContextualComposition.GrothendieckStep.AmbientRoutePaste
