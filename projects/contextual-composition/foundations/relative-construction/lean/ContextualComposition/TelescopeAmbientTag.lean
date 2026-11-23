module
public import ContextualComposition.TelescopeAmbientBase

@[expose] public section
namespace ContextualComposition.GrothendieckStep.TelescopeAmbientTag

open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite
open CoproductSpan SpanPull NativeCleavage TelescopeSquares ContextadAmbientPayload TelescopeAmbientBase
open scoped CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

universe i u v k j
variable {I : Type i} {B : Type u} [Category.{v} B] {K : I → Type k} [∀ t, Category.{j} (K t)]
variable (p d : ∀ t, K t ⥤ B) (C : ∀ t, Cleavage (p t)) {X Y : Bᵒᵖ ⥤ Cat.{v,u}}
variable (f : StrongTrans X.toPseudofunctor' Y.toPseudofunctor')

/-- On strict fibres, tagging commutes with the independently defined ambient payload functor. -/
theorem strictPayload (A : B) (t : I) :
    onFibre f (d t) (p t) A ⋙ strictTag p d Y A t =
      strictTag p d X A t ⋙ onFibre f (Sigma.desc d) (Sigma.desc p) A := by
  apply EvalPayload.cancelInclusion
  let J := Functor.Fiber.fiberInclusion (p := partProj p d X t) (S := A)
  exact (EvalPayload.fibrePaste (r := proj p d Y) A (atEndpoint f (d t)) (totalTag d Y t) (endpointOver f (d t) (p t)) rfl).trans
    ((congrArg (J ⋙ ·) (TelescopeGradeChange.totalMap_payload f (Sigma.incl t) (Sigma.desc d) (e := d t) rfl).symm).trans
      (EvalPayload.fibrePaste (p := partProj p d X t) A (totalTag d X t) (atEndpoint f (Sigma.desc d)) rfl (endpointOver f (Sigma.desc d) (Sigma.desc p))).symm)

/-- The tagged part and whole strict-fibre cells factor the same cartesian lift after transport across the strong square. -/
theorem strictCell {A D : B} (a : A ⟶ D) (t : I) (x : (partProj p d X t).Fiber D) :
    Aligned ((strictTag p d Y A t).map ((cartesianFace f (d t) (p t) (C t) a).sq.hom.app x))
      ((cartesianFace f (Sigma.desc d) (Sigma.desc p) (choice p C) a).sq.hom.app ((strictTag p d X D t).obj x)) := by
  let R := Route.ofChoice (weightedChoice p d C Y) a
  let T := totalTag d Y t
  let l := (cartesianFace f (d t) (p t) (C t) a).sq.hom.app x
  let z := (onFibre f (d t) (p t) D).obj x
  let w := (strictTag p d X D t).obj x
  let m := (cartesianFace f (Sigma.desc d) (Sigma.desc p) (choice p C) a).sq.hom.app w
  have hs := Functor.congr_obj (strictPayload p d f A t) ((Reindex.functor (partChoice p d C X t) a).obj x)
  have ht := Functor.congr_obj (strictPayload p d f D t) x
  let L := (strictTag p d Y A t).map l
  have hfac : Aligned (L.val ≫ R.lift ((strictTag p d Y D t).obj z))
      (m.val ≫ R.lift ((onFibre f (Sigma.desc d) (Sigma.desc p) D).obj w)) := by
    change Aligned (T.map l.val ≫ Reindex.lift (weightedChoice p d C Y) a ((strictTag p d Y D t).obj z)) _
    rw [← lift_tag p d C Y a t z]
    apply (NativeCube.ofEq (T.map_comp l.val (Reindex.lift (partChoice p d C Y t) a z)).symm).trans
    apply ((cartesianFace f (d t) (p t) (C t) a).fac x |>.map T).trans
    apply (NativeCube.functorAlign (TelescopeGradeChange.totalMap_payload f (Sigma.incl t) (Sigma.desc d) (e := d t) rfl).symm
      (Reindex.lift (partChoice p d C X t) a x)).trans
    exact ((cartesianFace f (Sigma.desc d) (Sigma.desc p) (choice p C) a).fac w).symm
  refine ⟨hs,congrArg R.act.obj ht,?_⟩
  simpa only [eqToHom_map] using NativeCube.cancelAligned (t := (strictTag p d Y D t).obj z) (t' := (onFibre f (Sigma.desc d) (Sigma.desc p) D).obj w) R L m hs ht hfac

/-- The alignment survives the strict fibre presentations on both sides of the tag. -/
theorem presentedCell {A D : B} (a : A ⟶ D) (t : I) (x : Total X (leg p d D t)) :
    Aligned ((presentedTag p d Y A t).map ((presented f (d t) (p t) (C t) a).hom.app x))
      ((presented f (Sigma.desc d) (Sigma.desc p) (choice p C) a).hom.app ((presentedTag p d X D t).obj x)) := by
  let y := (FibreTotal.into X (d t) (p t) D).obj x
  let O := FibreTotal.out Y (Sigma.desc d) (Sigma.desc p) A
  let W := (cartesianFace f (Sigma.desc d) (Sigma.desc p) (choice p C) a).sq.hom
  let l := (cartesianFace f (d t) (p t) (C t) a).sq.hom.app y
  have outTag : FibreTotal.out Y (d t) (p t) A ⋙ presentedTag p d Y A t = strictTag p d Y A t ⋙ O :=
    (congrArg (· ⋙ (strictTag p d Y A t ⋙ O)) (FibreTotal.out_into_functors Y (d t) (p t) A)).trans (Functor.id_comp _)
  have inTag := Functor.congr_obj (FibreTotal.out_into_functors X (Sigma.desc d) (Sigma.desc p) D) ((strictTag p d X D t).obj y)
  apply ((presented_component f (d t) (p t) (C t) a x).map (presentedTag p d Y A t)).trans
  apply (NativeCube.functorAlign outTag l).trans
  apply ((strictCell p d C f a t y).map O).trans
  apply ((FinalCube.Align.atEq W inTag.symm).map O).trans
  exact (presented_component f (Sigma.desc d) (Sigma.desc p) (choice p C) a ((presentedTag p d X D t).obj x)).symm

/-- The image of the part's cartesian comparison through the actual coproduct comparison agrees, with its endpoint transports, with the whole-span comparison. -/
theorem compareCell {A D : B} (a : A ⟶ D) (t : I) (x : Total X (leg p d D t)) :
    Aligned ((compare p d A Y).map ((Sigma.incl t).map ((presented f (d t) (p t) (C t) a).hom.app x)))
      ((presented f (Sigma.desc d) (Sigma.desc p) (choice p C) a).hom.app ((compare p d D X).obj ⟨t,x⟩)) :=
  (NativeCube.functorAlign (compareTag p d Y A t) ((presented f (d t) (p t) (C t) a).hom.app x)).trans
    ((presentedCell p d C f a t x).trans
      (FinalCube.Align.atEq (presented f (Sigma.desc d) (Sigma.desc p) (choice p C) a).hom (Functor.congr_obj (compareTag p d X D t).symm x)))

end ContextualComposition.GrothendieckStep.TelescopeAmbientTag
