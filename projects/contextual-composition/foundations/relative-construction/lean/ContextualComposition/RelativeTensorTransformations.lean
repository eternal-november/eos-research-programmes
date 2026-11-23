module
public import ContextualComposition.RelativeTensorUniversal

@[expose] public section
namespace ContextualComposition.RelativeTensor
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory
universe v u vF uF vG uG vD uD
variable {B : Type u} [Category.{v} B]
variable {F : LocallyDiscrete B ⥤ᵖ Cat.{vF,uF}} {G : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vG,uG}}
variable {D : Type uD} [Category.{vD} D] {H K : Tensor F G ⥤ D}
set_option backward.isDefEq.respectTransparency false

/-- Descend an independently specified cocone transformation to the original functors with the original vertex components. -/
def fromRestriction (a : Transformation (restrict H) (restrict K)) : H ⟶ K where
  app x := a.atVertex x.as
  naturality {x y} f := by
    have e := (Transformation.extend a).naturality f
    change (restrict H).extend.map f ≫ _ = _ ≫ (restrict K).extend.map f at e
    have h := Functor.congr_hom (extend_restrict H) f
    have k := Functor.congr_hom (extend_restrict K) f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at h k
    erw [h,k] at e
    exact e

/-- Isomorphic vertex components assemble to an invertible comparison of functors from the tensor. -/
noncomputable def isoFromRestriction (a : Transformation (restrict H) (restrict K))
    (h : ∀ x, IsIso (a.atVertex x)) : H ≅ K :=
  NatIso.ofComponents (fun X => @asIso _ _ _ _ (a.atVertex X.as) (h X.as))
    (fun f => (fromRestriction a).naturality f)

end ContextualComposition.RelativeTensor
