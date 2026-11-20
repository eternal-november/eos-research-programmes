module
public import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
public import Mathlib.CategoryTheory.Products.Basic
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableBicategoryAssembly
open CategoryTheory
open scoped CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
universe v w u
variable {B : Type u} (H : B → B → Type v) [I : ∀ x y, Category.{w} (H x y)]
structure Operations where
  unit : (x : B) → H x x
  multiply : ∀ {x y z}, H x y × H y z ⥤ H x z
  left : ∀ {x y} (f : H x y), multiply.obj (unit x,f) ≅ f
  right : ∀ {x y} (f : H x y), multiply.obj (f,unit y) ≅ f
  assoc : ∀ {x y z r} (f : H x y) (g : H y z) (h : H z r),
    multiply.obj (multiply.obj (f,g),h) ≅ multiply.obj (f,multiply.obj (g,h))
variable {H}
variable (O : Operations H)
abbrev cmp {x y z : B} (f : H x y) (g : H y z) := O.multiply.obj (f,g)
abbrev compCell {x y z : B} {f f' : H x y} {g g' : H y z} (s : f ⟶ f') (t : g ⟶ g') := O.multiply.map (X := (f,g)) (Y := (f',g')) (s,t)
abbrev rW {x y z : B} {f f' : H x y} (s : f ⟶ f') (g : H y z) := compCell O s (𝟙 g)
abbrev lW {x y z : B} (f : H x y) {g g' : H y z} (t : g ⟶ g') := compCell O (𝟙 f) t
structure Laws : Prop where
  leftNat : ∀ {x y} {f g : H x y} (t : f ⟶ g), lW O (O.unit x) t ≫ (O.left g).hom = (O.left f).hom ≫ t
  rightNat : ∀ {x y} {f g : H x y} (t : f ⟶ g), rW O t (O.unit y) ≫ (O.right g).hom = (O.right f).hom ≫ t
  assocFirst : ∀ {x y z r} {f f' : H x y} (t : f ⟶ f') (g : H y z) (h : H z r),
    rW O (rW O t g) h ≫ (O.assoc f' g h).hom = (O.assoc f g h).hom ≫ rW O t (cmp O g h)
  assocMiddle : ∀ {x y z r} (f : H x y) {g g' : H y z} (t : g ⟶ g') (h : H z r),
    rW O (lW O f t) h ≫ (O.assoc f g' h).hom = (O.assoc f g h).hom ≫ lW O f (rW O t h)
  assocLast : ∀ {x y z r} (f : H x y) (g : H y z) {h h' : H z r} (t : h ⟶ h'),
    lW O (cmp O f g) t ≫ (O.assoc f g h').hom = (O.assoc f g h).hom ≫ lW O f (lW O g t)
  triangle : ∀ {x y z} (f : H x y) (g : H y z),
    (O.assoc f (O.unit y) g).hom ≫ lW O f (O.left g).hom = rW O (O.right f).hom g
  pentagon : ∀ {x y z r s} (f : H x y) (g : H y z) (h : H z r) (i : H r s),
    rW O (O.assoc f g h).hom i ≫ (O.assoc f (cmp O g h) i).hom ≫ lW O f (O.assoc g h i).hom =
      (O.assoc (cmp O f g) h i).hom ≫ (O.assoc f g (cmp O h i)).hom
theorem cellId {x y z : B} (f : H x y) (g : H y z) : compCell O (𝟙 f) (𝟙 g) = 𝟙 (cmp O f g) :=
  O.multiply.map_id (f,g)
theorem cellComp {x y z : B} {f f' f'' : H x y} {g g' g'' : H y z}
    (r : f ⟶ f') (s : f' ⟶ f'') (v : g ⟶ g') (w : g' ⟶ g'') :
    compCell O (r ≫ s) (v ≫ w) = compCell O r v ≫ compCell O s w :=
  O.multiply.map_comp (X := (f,g)) (Y := (f',g')) (Z := (f'',g'')) (r,v) (s,w)
theorem leftRule {x y z : B} (f : H x y) {g g' g'' : H y z} (t : g ⟶ g') (v : g' ⟶ g'') :
    lW O f (t ≫ v) = lW O f t ≫ lW O f v := by rw [← cellComp,Category.id_comp]
theorem rightRule {x y z : B} {f f' f'' : H x y} (r : f ⟶ f') (s : f' ⟶ f'') (g : H y z) :
    rW O (r ≫ s) g = rW O r g ≫ rW O s g := by rw [← cellComp,Category.id_comp]
theorem exchange {x y z : B} {f f' : H x y} {g g' : H y z} (r : f ⟶ f') (s : g ⟶ g') :
    lW O f s ≫ rW O r g' = rW O r g ≫ lW O f' s := by rw [← cellComp,← cellComp,Category.id_comp,Category.comp_id,Category.id_comp,Category.comp_id]
theorem conjugate {C : Type*} [Category C] {a b x y : C} (t : a ⟶ b) (u : x ⟶ y) (f : a ≅ x) (g : b ≅ y)
    (h : t ≫ g.hom = f.hom ≫ u) : t = f.hom ≫ u ≫ g.inv := by
  apply (cancel_mono g.hom).mp
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id,h]
theorem conjugateReverse {C : Type*} [Category C] {a b x y : C} (t : a ⟶ b) (u : x ⟶ y) (f : a ≅ x) (g : b ≅ y)
    (h : t ≫ g.hom = f.hom ≫ u) : u = f.inv ≫ t ≫ g.hom := by
  rw [h,Iso.inv_hom_id_assoc]
@[instance_reducible] def build (D : Laws O) : Bicategory.{w,v} B where
  Hom := H
  id := O.unit
  comp := cmp O
  homCategory := I
  whiskerLeft := lW O
  whiskerRight := rW O
  associator := O.assoc
  leftUnitor := O.left
  rightUnitor := O.right
  whiskerLeft_id := cellId O
  whiskerLeft_comp := leftRule O
  id_whiskerLeft t := conjugate _ _ _ _ (D.leftNat t)
  comp_whiskerLeft := fun {_ _ _ _} f g {_ _} t => conjugate _ _ _ _ (D.assocLast f g t)
  id_whiskerRight := cellId O
  comp_whiskerRight := rightRule O
  whiskerRight_id t := conjugate _ _ _ _ (D.rightNat t)
  whiskerRight_comp t g h := conjugateReverse _ _ _ _ (D.assocFirst t g h)
  whisker_assoc := fun {_ _ _ _} f {_ _} t g => conjugate _ _ _ _ (D.assocMiddle f t g)
  whisker_exchange := exchange O
  pentagon := D.pentagon
  triangle := D.triangle
end ContextualComposition.GrothendieckStep.RepresentableBicategoryAssembly
