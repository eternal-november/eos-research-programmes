module
public import ContextualComposition.ContextadChartModifications
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadChosenCone
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks FibreValue TelescopeSquares NativeCleavage
set_option backward.isDefEq.respectTransparency false
universe u v
section Generic
variable {B K X : Type*} [Category* B] [Category* K] [Category* X] (Y : Bᵒᵖ ⥤ Cat.{v,u}) (e : K ⥤ B)
theorem alignChosen {x x' y y' : Total Y e} {l : x ⟶ y} {r : x' ⟶ y'}
    (t : y = y') (g : Aligned (gradeMap l) (gradeMap r))
    (p : Pure (payloadMap l)) (q : Pure (payloadMap r)) : Aligned l r := by
  subst y'
  obtain ⟨⟨⟨a⟩,⟨b⟩⟩⟩ := x; obtain ⟨⟨⟨a'⟩,⟨b'⟩⟩⟩ := x'
  have h : a = a' := g.src; subst a'
  have hg := g.eq
  have hb := p.choose.trans ((congrArg (fun k => (Y.map (e.map k).op).toFunctor.obj (payload _ _ y)) hg).trans q.choose.symm)
  change b = b' at hb; subst b'
  exact NativeCube.ofEq (WeightedCells.pureArrowEq Y e hg p q)
variable {D C T : Type*} [Category* D] [Category* C] [Category* T]
variable (π : D ⥤ T) {F G H J : C ⥤ D} (l : F ⟶ H) (r : G ⟶ J)
theorem coneExt (base : F ⋙ π = G ⋙ π) (target : H = J)
    (v : ∀ x, Aligned (l.app x) (r.app x)) (c : ∀ x, Cartesian π (r.app x)) : F = G := by
  subst J
  let h (x : C) := (v x).src
  have fac (x : C) : eqToHom (h x) ≫ r.app x = l.app x := by simpa using (v x).comm.symm
  fapply Functor.ext
  · exact h
  · intro x y f
    apply ContextadOuterCharts.cancel π (l.app y) (by
      rw [← fac]; exact pasteCart (ContextadCartesian.vertical_cart _) (c _))
    · simpa only [Functor.map_comp,eqToHom_map,Functor.comp_map] using Functor.congr_hom base f
    · rw [l.naturality,← fac x,← fac y]
      simp only [Category.assoc,eqToHom_trans_assoc,eqToHom_refl,Category.id_comp,r.naturality]
theorem conePure {F G H J : X ⥤ Total Y e} (l : F ⟶ H) (r : G ⟶ J)
    (base : F ⋙ gradeProjection = G ⋙ gradeProjection) (target : H = J)
    (g : ∀ x, Aligned (gradeMap (l.app x)) (gradeMap (r.app x)))
    (p : ∀ x, Pure (payloadMap (l.app x))) (q : ∀ x, Pure (payloadMap (r.app x))) :
    F = G := by
  apply coneExt gradeProjection l r base target
  · exact fun x => alignChosen Y e (Functor.congr_obj target x) (g x) (p x) (q x)
  · intro x; obtain ⟨h,k⟩ := q x
    have : IsIso (payloadMap (r.app x)) := by rw [k]; infer_instance
    exact ContextadCartesian.cart_of_payload Y e _
end Generic
end ContextualComposition.GrothendieckStep.ContextadChosenCone
