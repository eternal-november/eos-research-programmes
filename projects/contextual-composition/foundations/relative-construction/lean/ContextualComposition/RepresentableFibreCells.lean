module
public import ContextualComposition.RepresentableKleisliData
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableFibreCells
open CategoryTheory CategoryTheory.Bicategory Opposite CategoryTheory.Functor
open AmbientBicategory AmbientRoundTrip RepresentableKleisli
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
universe u
variable {B : Type u} [Category.{u} B]
variable {U V W : Obj.{u,u} B} {f g h : U ⟶ V} (A : B) (x : (underlying U).obj (op A))
theorem vertical (a : f ⟶ g) (b : g ⟶ h) : component (a ≫ b) A x = component a A x ≫ component b A x := rfl
theorem right (a : f ⟶ g) (b : V ⟶ W) : component (a ▷ b) A x = (compAt b.hom A).map (component a A x) := rfl
theorem left (a : U ⟶ V) {b c : V ⟶ W} (t : b ⟶ c) : component (a ◁ t) A x = component t A ((compAt a.hom A).obj x) := rfl
section Serial
variable {R : Obj.{u,u} B} {a b : V ⟶ W}
variable (t : f ⟶ g) (s : a ⟶ b) (m : W ⟶ R)
theorem serial : component (((t ▷ a) ≫ g ◁ s) ▷ m) A x =
    (compAt m.hom A).map ((compAt a.hom A).map (component t A x) ≫ component s A ((compAt g.hom A).obj x)) := rfl
end Serial
variable {P : Endpoints.{u,u,u,u} B} {S : P.Split} {J D : B} {f g : KH S J D}
theorem rowMap (t : f ⟶ g) : (fibreEquiv (S := S) (A := J) (D := D)).functor.map t = component t J (Discrete.mk (𝟙 J)) := rfl
end ContextualComposition.GrothendieckStep.RepresentableFibreCells
