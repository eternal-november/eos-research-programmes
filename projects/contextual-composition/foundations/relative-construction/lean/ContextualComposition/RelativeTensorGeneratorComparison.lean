module
public import ContextualComposition.RelativeTensorTransformations

@[expose] public section
namespace ContextualComposition.RelativeTensor
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory
universe v u vF uF vG uG vD uD
variable {B : Type u} [Category.{v} B]
variable {F : LocallyDiscrete B ⥤ᵖ Cat.{vF,uF}} {G : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vG,uG}}
variable {D : Type uD} [Category.{vD} D]
set_option backward.isDefEq.respectTransparency false

/-- Natural isomorphisms out of the tensor can be specified on product objects, product arrows and forward balances. -/
def isoOfGenerators {H K : Tensor F G ⥤ D} (p : ∀ x, H.obj x ≅ K.obj x)
    (native : ∀ {i : B} {x x' : F.obj ⟨i⟩} {y y' : G.obj ⟨op i⟩} (f : x ⟶ x') (g : y ⟶ y'),
      H.map ((insertion F G i).map (productMap f g)) ≫ (p _).hom =
        (p _).hom ≫ K.map ((insertion F G i).map (productMap f g)))
    (bal : ∀ {i j : B} (u : i ⟶ j) (x : F.obj ⟨i⟩) (y : G.obj ⟨op j⟩),
      H.map (balancing F G u x y).hom ≫ (p _).hom = (p _).hom ≫ K.map (balancing F G u x y).hom) :
    H ≅ K :=
  NatIso.ofComponents p (by
    intro X Y f
    let q : Transformation (restrict H) (restrict K) := {
      components := fun _ => { app := fun _ => (p _).hom, naturality := fun _ _ h => native h.1 h.2 }
      square := bal }
    exact (fromRestriction q).naturality f)

theorem extGenerators {H K : Tensor F G ⥤ D} (h : ∀ x, H.obj x = K.obj x)
    (native : ∀ {i : B} {x x' : F.obj ⟨i⟩} {y y' : G.obj ⟨op i⟩} (f : x ⟶ x') (g : y ⟶ y'),
      H.map ((insertion F G i).map (productMap f g)) ≫ eqToHom (h _) =
        eqToHom (h _) ≫ K.map ((insertion F G i).map (productMap f g)))
    (bal : ∀ {i j : B} (u : i ⟶ j) (x : F.obj ⟨i⟩) (y : G.obj ⟨op j⟩),
      H.map (balancing F G u x y).hom ≫ eqToHom (h _) = eqToHom (h _) ≫ K.map (balancing F G u x y).hom) : H = K :=
  Functor.ext_of_iso (isoOfGenerators (fun x => eqToIso (h x)) native bal) h (fun _ => rfl)
end ContextualComposition.RelativeTensor
