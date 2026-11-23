module

public import ContextualComposition.BicyclicAssembly
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic

/-! Bicategorical part of the bicyclic obstruction. The shadow used in
the proof identifies 1-cells connected by an invertible 2-cell. Fullness
from a discrete hom-category reflects equality from that identification. -/

@[expose] public section
namespace ContextualComposition.BicyclicLocalFullness
open CategoryTheory Bicategory BicyclicAssembly
universe u v w
variable {B : Type u} [Bicategory.{w,v} B]

structure Shadow (B : Type u) where
  obj : B

def isomorphic (x y : B) : Setoid (x ⟶ y) where
  r f g := Nonempty (f ≅ g)
  iseqv := ⟨fun f => ⟨Iso.refl f⟩,fun ⟨e⟩ => ⟨e.symm⟩,fun ⟨e⟩ ⟨e'⟩ => ⟨e ≪≫ e'⟩⟩

abbrev Hom (x y : B) := Quotient (isomorphic x y)
def read {x y : B} (f : x ⟶ y) : Hom x y := Quotient.mk _ f

def compose {x y z : B} (p : Hom x y) (q : Hom y z) : Hom x z :=
  Quotient.liftOn₂ p q (fun f g => read (f ≫ g)) (by
    rintro f g f' g' ⟨e⟩ ⟨k⟩
    exact Quotient.sound ⟨whiskerRightIso e g ≪≫ whiskerLeftIso f' k⟩)

instance : Category (Shadow B) where
  Hom x y := Hom x.obj y.obj
  id x := read (𝟙 x.obj)
  comp := compose
  id_comp f := Quotient.inductionOn f fun g => Quotient.sound ⟨λ_ g⟩
  comp_id f := Quotient.inductionOn f fun g => Quotient.sound ⟨ρ_ g⟩
  assoc f g h := Quotient.inductionOn₃ f g h fun i j k => Quotient.sound ⟨α_ i j k⟩

variable {A : Type*} [Category* A]

def induced (F : LocallyDiscrete A ⥤ᵖ B) : A ⥤ Shadow B where
  obj x := ⟨F.obj ⟨x⟩⟩
  map f := read (F.map ⟨f⟩)
  map_id x := Quotient.sound ⟨F.mapId ⟨x⟩⟩
  map_comp f g := Quotient.sound ⟨F.mapComp ⟨f⟩ ⟨g⟩⟩

/-- An isomorphism of images supplies a morphism between the two source
arrows under fullness. Discreteness forces the source arrows to coincide. -/
theorem reflect (F : LocallyDiscrete A ⥤ᵖ B) {x y : A}
    (h : (F.mapFunctor ⟨x⟩ ⟨y⟩).Full) {f g : x ⟶ y}
    (e : (induced F).map f = (induced F).map g) : f = g := by
  have he : Nonempty (F.map (Discrete.mk f) ≅ F.map (Discrete.mk g)) := Quotient.exact e
  obtain ⟨i⟩ := he
  let k : Discrete.mk f ⟶ Discrete.mk g := (F.mapFunctor ⟨x⟩ ⟨y⟩).preimage i.hom
  exact Discrete.eq_of_hom k

abbrev Point := LocallyDiscrete.mk point

/-- These are just the object equivalence and generator naturality square
of coherent agreement on the common pure category. The calculation needs
only these components, so no higher compatibility is assumed as a premise. -/
theorem no_locally_full_assembly (F G : LocallyDiscrete (SingleObj Bicyclic) ⥤ᵖ B)
    (q : F.obj Point ⟶ G.obj Point) (r : G.obj Point ⟶ F.obj Point)
    (qr : q ≫ r ≅ 𝟙 _) (rq : r ≫ q ≅ 𝟙 _)
    (natural : F.map (Discrete.mk low) ≫ q ≅ q ≫ G.map (Discrete.mk high)) :
    ¬ (F.mapFunctor Point Point).Full ∧ ¬ (G.mapFunctor Point Point).Full := by
  let i : (induced F).obj point ≅ (induced G).obj point :=
    ⟨read q,read r,Quotient.sound ⟨qr⟩,Quotient.sound ⟨rq⟩⟩
  have h : (induced F).map low ≫ i.hom = i.hom ≫ (induced G).map high :=
    Quotient.sound ⟨natural⟩
  have e := common_collapse (induced F) (induced G) i h
  exact ⟨fun full => low_high_ne (reflect F full e.1),fun full => low_high_ne (reflect G full e.2)⟩

abbrev purePoint := LocallyDiscrete.mk (SingleObj.star Pure)

/-- A strong natural comparison on the whole pure category whose component
is an adjoint equivalence supplies the requisite transport automatically. -/
theorem coherent_pure_obstruction (F G : LocallyDiscrete (SingleObj Bicyclic) ⥤ᵖ B)
    (s : Pseudofunctor.StrongTrans (leftPure.toPseudofunctor.comp F) (rightPure.toPseudofunctor.comp G))
    (q : Bicategory.Equivalence (F.obj Point) (G.obj Point)) (at_point : q.hom = s.app purePoint) :
    ¬ (F.mapFunctor Point Point).Full ∧ ¬ (G.mapFunctor Point Point).Full := by
  let a : purePoint ⟶ purePoint := Discrete.mk (show Pure from Multiplicative.ofAdd (1 : Nat))
  have left : (leftPure.toPseudofunctor.comp F).map a = F.map (Discrete.mk low) := by
    change F.map (Discrete.mk (show point ⟶ point from down ^ (1 : Nat))) = _
    rw [pow_one]
  have right : (rightPure.toPseudofunctor.comp G).map a = G.map (Discrete.mk high) := by
    change G.map (Discrete.mk (show point ⟶ point from up ^ (1 : Nat))) = _
    rw [pow_one]
  apply no_locally_full_assembly F G q.hom q.inv q.unit.symm q.counit
  have cell := s.naturality a
  erw [left,right,← at_point] at cell
  exact cell

end ContextualComposition.BicyclicLocalFullness
