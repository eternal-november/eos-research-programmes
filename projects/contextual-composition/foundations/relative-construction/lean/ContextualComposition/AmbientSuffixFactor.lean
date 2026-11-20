module
public import ContextualComposition.AmbientInsideMateRead
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientSuffixFactor
open CategoryTheory CategoryTheory.Functor Opposite FibreValue TelescopeSquares
open ContextadAmbientPayload ContextadWeakAction ContextadWeakWeight ContextadOuterCharts AmbientMateReindex
open CategoryTheory.Pseudofunctor SpanApex BoundaryPaste
open scoped CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 550000
universe u v
variable {B K L J : Type u} [Category.{v} B] [Category.{v} K] [Category.{v} L] [Category.{v} J]
variable {Y Z : Bᵒᵖ ⥤ Cat.{v,u}} (a : StrongTrans Y.toPseudofunctor' Z.toPseudofunctor')
variable (d : J ⥤ B) (e : K ⥤ J) (w : L ⥤ J) (r : K ⥤ L) (l : r ⋙ w ⟶ e)
abbrev pull (G : Bᵒᵖ ⥤ Cat.{v,u}) {A : Type u} [Category.{v} A] (t : A ⥤ J) := SpanPayload.totalMap G t d rfl
noncomputable abbrev square := AmbientMateCalculus.q (e ⋙ d) (w ⋙ d) r (whiskerRight l d) a
theorem leafLift (G : Bᵒᵖ ⥤ Cat.{v,u}) (x : Total G (e ⋙ d)) :
    (leafAt G d).map ((liftTail G d r l).app x) = (tip G (e ⋙ d) (w ⋙ d) r (whiskerRight l d)).app x := rfl
theorem trimHead {C : Type*} [Category* C] {x y z : C} (h : x ⟶ y) (k : y ⟶ z) (p : Pure h) : Aligned (h ≫ k) k := by
  obtain ⟨t,s⟩ := p; subst y; simpa [s] using Aligned.refl k
theorem parts {x y x' y' : Total Z d} (v : x ⟶ y) (w : x' ⟶ y') (s : x=x') (t : y=y')
    (g : Aligned (gradeMap v) (gradeMap w)) (l : Aligned ((leafAt Z d).map v) ((leafAt Z d).map w)) : Aligned v w := by
  subst x'; subst y'; exact NativeCube.ofEq (AmbientMateCalculus.foldEqual d g.eq l.eq)
theorem natural (x : Total Y (e ⋙ d)) :
    Aligned ((pull d Z w).map ((square a d e w r l).app x) ≫ (liftTail Z d r l).app ((atEndpoint a (e ⋙ d)).obj x))
      ((atEndpoint a d).map ((liftTail Y d r l).app x)) := by
  let t := (square a d e w r l).app x
  let z := (atEndpoint a (e ⋙ d)).obj x
  let k := (pull d Z w).map t
  let u := (liftTail Y d r l).app x
  let v := (liftTail Z d r l).app z
  apply parts d (k ≫ v) ((atEndpoint a d).map u)
  · exact Functor.congr_obj (actionPull a d w rfl).symm _
  · exact Functor.congr_obj (actionPull a d e rfl).symm x
  · have h : Pure (gradeMap k) := pureMap w (weakGrade (e ⋙ d) (w ⋙ d) r (whiskerRight l d) a x)
    have j := ContextadPayloadModification.appChange l (Functor.congr_obj (actionGrade (e ⋙ d) (totalStrong a) (strongOver a)) x)
    exact (trimHead (gradeMap k) (gradeMap v) h).trans (j.trans (NativeCube.functorAlign (actionGrade d (totalStrong a) (strongOver a)) u).symm)
  · rw [Functor.map_comp,show (leafAt Z d).map v = _ from leafLift d e w r l Z z]
    exact (AmbientMateCalculus.factor (e ⋙ d) (w ⋙ d) r (whiskerRight l d) a x).trans (NativeCube.functorAlign (actionLeaf d (totalStrong a) (strongOver a)) u).symm
end ContextualComposition.GrothendieckStep.AmbientSuffixFactor
