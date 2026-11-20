module
public import ContextualComposition.RepresentableBicategoryAssembly
public import ContextualComposition.RepresentableKleisliFunctor
public import Mathlib.CategoryTheory.Functor.FullyFaithful
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableComparisonTransport
open CategoryTheory CategoryTheory.Bicategory
open RepresentableKleisli (horizontal horizontal_id horizontal_comp)
open scoped CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
universe u v w z q
variable {B : Type u} [Bicategory.{w,v} B] (H : B → B → Type z) [∀ x y, Category.{q} (H x y)]
structure Data where
  unit : (x : B) → H x x
  mult : ∀ {x y z}, H x y × H y z ⥤ H x z
  hom : ∀ x y, H x y ⥤ (x ⟶ y)
  fullfaithful : ∀ x y, (hom x y).FullyFaithful
  unitIso : ∀ x, (hom x x).obj (unit x) ≅ 𝟙 x
  cmpIso : ∀ {x y z} (f : H x y) (g : H y z),
    (hom x z).obj (mult.obj (f,g)) ≅ (hom x y).obj f ≫ (hom y z).obj g
  cmpNat : ∀ {x y z} {f f' : H x y} {g g' : H y z} (s : f ⟶ f') (t : g ⟶ g'),
    (hom x z).map (mult.map (X := (f,g)) (Y := (f',g')) (s,t)) ≫ (cmpIso f' g').hom =
      (cmpIso f g).hom ≫ horizontal ((hom x y).map s) ((hom y z).map t)
variable {H} (D : Data H)
abbrev X {x y : B} (h : H x y) := (D.hom x y).obj h
abbrev Y {x y : B} {f g : H x y} (t : f ⟶ g) := (D.hom x y).map t
abbrev cmp {x y z : B} (f : H x y) (g : H y z) := D.mult.obj (f,g)
abbrev W {x y z : B} {f f' : H x y} {g g' : H y z} (s : f ⟶ f') (t : g ⟶ g') :=
  D.mult.map (X := (f,g)) (Y := (f',g')) (s,t)
def leftImage {x y : B} (f : H x y) :=
  D.cmpIso (D.unit x) f ≪≫ whiskerRightIso (D.unitIso x) (X D f) ≪≫ (λ_ (X D f))
def rightImage {x y : B} (f : H x y) :=
  D.cmpIso f (D.unit y) ≪≫ whiskerLeftIso (X D f) (D.unitIso y) ≪≫ (ρ_ (X D f))
def head {x y z r : B} (f : H x y) (g : H y z) (h : H z r) :=
  D.cmpIso (cmp D f g) h ≪≫ whiskerRightIso (D.cmpIso f g) (X D h)
def tail {x y z r : B} (f : H x y) (g : H y z) (h : H z r) :=
  D.cmpIso f (cmp D g h) ≪≫ whiskerLeftIso (X D f) (D.cmpIso g h)
def assocImage {x y z r : B} (f : H x y) (g : H y z) (h : H z r) :=
  head D f g h ≪≫ (α_ (X D f) (X D g) (X D h)) ≪≫ (tail D f g h).symm
def ops : RepresentableBicategoryAssembly.Operations H where
  unit := D.unit
  multiply := fun {_ _ _} => D.mult
  left := fun {x y} f => (D.fullfaithful x y).preimageIso (leftImage D f)
  right := fun {x y} f => (D.fullfaithful x y).preimageIso (rightImage D f)
  assoc := fun {x _ _ w} f g h => (D.fullfaithful x w).preimageIso (assocImage D f g h)
theorem leftPort {x y : B} (f : H x y) : Y D ((ops D).left f).hom = (leftImage D f).hom :=
  (D.fullfaithful x y).map_preimage _
theorem rightPort {x y : B} (f : H x y) : Y D ((ops D).right f).hom = (rightImage D f).hom :=
  (D.fullfaithful x y).map_preimage _
theorem assocPort {x y z r : B} (f : H x y) (g : H y z) (h : H z r) :
    Y D ((ops D).assoc f g h).hom = (assocImage D f g h).hom :=
  (D.fullfaithful x r).map_preimage _
theorem cellPort {x y z : B} {f f' : H x y} {g g' : H y z} (s : f ⟶ f') (t : g ⟶ g') :
    Y D (W D s t) = (D.cmpIso f g).hom ≫ horizontal (Y D s) (Y D t) ≫ (D.cmpIso f' g').inv :=
  RepresentableBicategoryAssembly.conjugate _ _ _ _ (D.cmpNat s t)
theorem leftCell {x y z : B} (f : H x y) {g g' : H y z} (t : g ⟶ g') :
    Y D (W D (𝟙 f) t) = (D.cmpIso f g).hom ≫ X D f ◁ Y D t ≫ (D.cmpIso f g').inv := by
  rw [cellPort]
  simp only [Functor.map_id,horizontal,id_whiskerRight,Category.id_comp]
theorem rightCell {x y z : B} {f f' : H x y} (t : f ⟶ f') (g : H y z) :
    Y D (W D t (𝟙 g)) = (D.cmpIso f g).hom ≫ Y D t ▷ X D g ≫ (D.cmpIso f' g).inv := by
  rw [cellPort]
  simp only [Functor.map_id,horizontal,whiskerLeft_id,Category.comp_id]
end ContextualComposition.GrothendieckStep.RepresentableComparisonTransport
