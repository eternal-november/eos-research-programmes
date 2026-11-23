module
public import Mathlib.CategoryTheory.Category.Cat.AsSmall
public import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor

@[expose] public section
namespace ContextualComposition.Factorization.Endpoint.UniverseLift
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
open scoped CategoryTheory.Bicategory
universe w v u v' u'
variable {A : Type u} {B : Type u'} [Category.{v} A] [Category.{v'} B]

/-- Raise the two endpoints of a functor into small categories, even when their original sizes differ. -/
abbrev map (F : A ⥤ B) : AsSmall.{w} A ⥤ AsSmall.{w} B := AsSmall.down ⋙ F ⋙ AsSmall.up

def cell {F G : A ⥤ B} (η : F ⟶ G) : map.{w} F ⟶ map.{w} G where
  app X := ⟨η.app (ULift.down X)⟩
  naturality _ _ f := congrArg ULift.up (η.naturality (ULift.down f))

def iso {F G : A ⥤ B} (h : F ≅ G) : map.{w} F ≅ map.{w} G where
  hom := cell h.hom
  inv := cell h.inv
  hom_inv_id := by ext X; exact congrArg ULift.up (h.hom_inv_id_app (ULift.down X))
  inv_hom_id := by ext X; exact congrArg ULift.up (h.inv_hom_id_app (ULift.down X))

/-- The bicategorical action of the ordinary small-category universe lift has identity component constraints. -/
def pseudofunctor : Cat.{v,u} ⥤ᵖ Cat.{max w v u,max w v u} where
  obj A := Cat.of (AsSmall.{w} A)
  map f := (map f.toFunctor).toCatHom
  map₂ η := (cell η.toNatTrans).toCatHom₂
  map₂_id f := rfl
  map₂_comp η θ := rfl
  mapId A := Iso.refl _
  mapComp f g := Iso.refl _
  map₂_whisker_left := by intros; apply Cat.Hom₂.ext; apply NatTrans.ext; funext x; apply ULift.ext; change _ = 𝟙 _ ≫ _ ≫ 𝟙 _; erw [Category.id_comp, Category.comp_id]; rfl
  map₂_whisker_right := by intros; apply Cat.Hom₂.ext; apply NatTrans.ext; funext x; apply ULift.ext; change _ = 𝟙 _ ≫ _ ≫ 𝟙 _; erw [Category.id_comp, Category.comp_id]; rfl
  map₂_associator := by intros; apply Cat.Hom₂.ext; apply NatTrans.ext; funext x; apply ULift.ext; change 𝟙 _ = 𝟙 _ ≫ _ ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _; simp; rfl
  map₂_left_unitor := by intros; apply Cat.Hom₂.ext; apply NatTrans.ext; funext x; apply ULift.ext; change 𝟙 _ = 𝟙 _ ≫ _ ≫ 𝟙 _; simp; rfl
  map₂_right_unitor := by intros; apply Cat.Hom₂.ext; apply NatTrans.ext; funext x; apply ULift.ext; change 𝟙 _ = 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _; simp

end ContextualComposition.Factorization.Endpoint.UniverseLift
