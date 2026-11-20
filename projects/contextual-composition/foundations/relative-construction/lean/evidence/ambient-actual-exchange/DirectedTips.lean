import ContextualComposition.AmbientPackedTips
open CategoryTheory CategoryTheory.Functor ContextualComposition.GrothendieckStep
open ContextadModification FibreValue TelescopeSquares NativeBlocks ContextadRoutes ContextadLawTransport
open AmbientCoordinates AmbientBicategory AmbientPackedTips ContextadWeakWeight ContextadWeakAction ContextadAmbientPayload
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
namespace ExchangeReview.Directed
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 750000
attribute [local irreducible] BlockEvaluation.global ContextadAmbientPayload.totalStrong
theorem isoAcross {C : Type*} [Category* C] {a b c d : C} {u : a ⟶ b} {v : c ⟶ d} (e : Aligned u v) (h : IsIso u) : IsIso v := by
  obtain ⟨rfl,rfl,p⟩ := e; simp at p; exact p ▸ h
theorem notAbove {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {a b : C} {s t : D} {u : a ⟶ b} {v : s ⟶ t} (h : Aligned (F.map u) v) (bad : ¬ IsIso v) : ¬ IsIso u :=
  fun q => bad (isoAcross h (by letI := q; infer_instance))
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (X : Obj.{u,v} B) (f g : Map S 2 1) (pg : gradeCart g)
variable (x : Raw S X 4)
noncomputable abbrev z := ((I (S := S) X).obj x)
noncomputable abbrev nextAt := (atEndpoint (oper S g pg X).hom (E (S := S) 2)).obj (z X x)
noncomputable abbrev baseLeg := f.leg.app (ft (S := S) X x)
theorem inDirected (bad : ¬ IsIso (baseLeg X f x)) :
    ¬ IsIso (tipAt f (obj S 2 X) (z X x)) := by
  apply notAbove (proj (underlying (obj S 2 X))) _ bad
  apply (NativeCube.ofEq (tipBase _ _ _ f.grade f.leg _)).trans
  exact ContextadPayloadModification.appChange f.leg (inIndex X x).symm
theorem outDirected (bad : ¬ IsIso (baseLeg X f x)) :
    ¬ IsIso (tipAt f (obj S 1 X) (nextAt X g pg x)) := by
  apply notAbove (proj (underlying (obj S 1 X))) _ bad
  apply (NativeCube.ofEq (tipBase _ _ _ f.grade f.leg _)).trans
  apply ContextadPayloadModification.appChange f.leg
  exact (Functor.congr_obj (actionGrade (E (S := S) 2) (totalStrong (oper S g pg X).hom) (strongOver (oper S g pg X).hom)) (z X x)).trans (inIndex X x).symm
section FixedCones
open ContextadDisjointCut SpanApex
variable (z₀ : (power S 4).apex)
theorem leftBase : Aligned ((left P).map ((ContextadDisjointCut.leftCone f g).app z₀)) (f.leg.app ((blocks S 2 2).first.obj z₀)) :=
  (((leftTip f g z₀).map (left P)).trans (NativeCube.functorAlign g.over ((move f).app z₀))).trans
    (NativeCube.ofEq (moveBase f z₀))
theorem conesDirected (bad : ¬ IsIso (f.leg.app ((blocks S 2 2).first.obj z₀))) :
    ¬ IsIso ((ContextadDisjointCut.leftCone f g).app z₀) ∧ ¬ IsIso ((ContextadDisjointCut.rightCone f g).app z₀) :=
  ⟨notAbove (left P) (leftBase f g z₀) bad,
   notAbove (left P) ((coneBase f g z₀).symm.trans (leftBase f g z₀)) bad⟩
end FixedCones
end ExchangeReview.Directed
#print axioms ExchangeReview.Directed.inDirected
#print axioms ExchangeReview.Directed.outDirected
