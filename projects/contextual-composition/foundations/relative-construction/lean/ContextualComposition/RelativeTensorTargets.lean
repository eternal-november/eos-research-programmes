module
public import ContextualComposition.RelativeTensorUniversal

@[expose] public section
namespace ContextualComposition.RelativeTensor
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory
universe v u vF uF vG uG vD uD vE uE
variable {B : Type u} [Category.{v} B]
variable {F : LocallyDiscrete B ⥤ᵖ Cat.{vF,uF}} {G : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vG,uG}}
variable {D : Type uD} [Category.{vD} D] {E : Type uE} [Category.{vE} E]
set_option backward.isDefEq.respectTransparency false

def postcompose (S : Cocone F G D) (H : D ⥤ E) : Cocone F G E where
  fiber i := S.fiber i ⋙ H
  bal u x y := H.mapIso (S.bal u x y)
  natural := by
    intro i j u x x' y y' p q
    exact (H.map_comp _ _).symm.trans ((congrArg H.map (S.natural u p q)).trans (H.map_comp _ _))
  unit x y := congrArg H.map (S.unit x y)
  comp u v x y := by
    have h := congrArg H.map (S.comp u v x y)
    simp only [H.map_comp] at h
    exact h

def postFunctor (H : D ⥤ E) : Cocone F G D ⥤ Cocone F G E where
  obj S := postcompose S H
  map a := ⟨fun i => Functor.whiskerRight (a.components i) H, fun u x y =>
    (H.map_comp _ _).symm.trans ((congrArg H.map (a.square u x y)).trans (H.map_comp _ _))⟩
  map_id S := by apply Transformation.ext; funext i; exact Functor.whiskerRight_id _
  map_comp f g := by apply Transformation.ext; funext i; exact Functor.whiskerRight_comp _ _ _

/-- Restriction along the quotient generators commutes with target change for all diagrams and all their transformations. -/
theorem restrict_postFunctor (H : D ⥤ E) :
    (Functor.whiskeringRight (Tensor F G) D E).obj H ⋙ restrictFunctor = restrictFunctor ⋙ postFunctor H := rfl

theorem extend_post (S : Cocone F G D) (H : D ⥤ E) : (postcompose S H).extend = S.extend ⋙ H := by
  apply CategoryTheory.Quotient.lift_unique'
  fapply Paths.ext_functor
  · rfl
  intro x y f
  change (postcompose S H).extend.map ((quotient F G).map (generator F G f)) =
    𝟙 _ ≫ H.map (S.extend.map ((quotient F G).map (generator F G f))) ≫ 𝟙 _
  erw [Category.id_comp, Category.comp_id, Cocone.extend_generator, Cocone.extend_generator]
  cases f <;> rfl

end ContextualComposition.RelativeTensor
