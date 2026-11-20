module
public import ContextualComposition.RepresentableBicategoryAssembly
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentablePureBuilder
open CategoryTheory
open RepresentableBicategoryAssembly
open scoped CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
universe u v w s t
variable {B : Type u} {H : B → B → Type v} [∀ x y, Category.{w} (H x y)]
variable {A : Type s} [Category.{t} A]
variable (O : Operations H)
structure Faces where
  obj : A → B
  map : ∀ {x y : A}, (x ⟶ y) → H (obj x) (obj y)
  unit : ∀ x : A, map (𝟙 x) ≅ O.unit (obj x)
  comp : ∀ {x y z : A} (f : x ⟶ y) (g : y ⟶ z), RepresentableBicategoryAssembly.cmp O (map f) (map g) ≅ map (f ≫ g)
  assoc : ∀ {x y z r : A} (f : x ⟶ y) (g : y ⟶ z) (h : z ⟶ r),
    (O.assoc (map f) (map g) (map h)).hom ≫ lW O (map f) (comp g h).hom ≫ (comp f (g ≫ h)).hom =
      rW O (comp f g).hom (map h) ≫ (comp (f ≫ g) h).hom ≫
        eqToHom (congrArg (fun j => map j) (Category.assoc f g h))
  left : ∀ {x y : A} (f : x ⟶ y),
    (comp (𝟙 x) f).hom ≫ eqToHom (congrArg (fun j => map j) (Category.id_comp f)) =
      rW O (unit x).hom (map f) ≫ (O.left (map f)).hom
  right : ∀ {x y : A} (f : x ⟶ y),
    (comp f (𝟙 y)).hom ≫ eqToHom (congrArg (fun j => map j) (Category.comp_id f)) =
      lW O (map f) (unit y).hom ≫ (O.right (map f)).hom
variable {O} (L : Laws O) (F : Faces (A := A) O)
def buildPure : @Pseudofunctor (LocallyDiscrete A) _ B (build O L) := by
  letI : Bicategory B := build O L
  refine LocallyDiscrete.mkPseudofunctor F.obj (fun {_ _} => F.map) F.unit (fun f g => (F.comp f g).symm) ?_ ?_ ?_
  · intro x y z r f g h
    change (F.comp (f ≫ g) h).inv ≫ rW O (F.comp f g).inv (F.map h) ≫
        (O.assoc (F.map f) (F.map g) (F.map h)).hom ≫
          lW O (F.map f) (F.comp g h).hom ≫ (F.comp f (g ≫ h)).hom = _
    have W : rW O (F.comp f g).inv (F.map h) ≫ rW O (F.comp f g).hom (F.map h) = 𝟙 _ := by
      rw [← rightRule,Iso.inv_hom_id]
      exact cellId O (F.map (f ≫ g)) (F.map h)
    rw [F.assoc f g h,← Category.assoc (rW O (F.comp f g).inv (F.map h)),W,Category.id_comp,Iso.inv_hom_id_assoc]
  · intro x y f
    change (F.comp (𝟙 x) f).inv ≫ rW O (F.unit x).hom (F.map f) ≫ (O.left (F.map f)).hom = _
    rw [← F.left f,Iso.inv_hom_id_assoc]
  · intro x y f
    change (F.comp f (𝟙 y)).inv ≫ lW O (F.map f) (F.unit y).hom ≫ (O.right (F.map f)).hom = _
    rw [← F.right f,Iso.inv_hom_id_assoc]
end ContextualComposition.GrothendieckStep.RepresentablePureBuilder
