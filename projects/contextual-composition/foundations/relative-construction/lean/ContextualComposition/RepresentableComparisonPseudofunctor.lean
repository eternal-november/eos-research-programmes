module
public import ContextualComposition.RepresentableComparisonTriangle
public import ContextualComposition.RepresentableComparisonEquivalences
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableComparisonPseudofunctor
open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Pseudofunctor
open RepresentableComparisonTransport RepresentableBicategoryAssembly
open RepresentableKleisli (horizontal)
open scoped CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
universe u v w z q
variable {B : Type u} [Bicategory.{w,v} B] {H : B → B → Type z} [∀ x y, Category.{q} (H x y)]
variable (D : Data H)
structure Source where
  as : B
  tagged : D = D := rfl
abbrev sourceHom (a b : Source D) := H a.as b.as
def sourceOps : Operations (sourceHom D) where
  unit a := D.unit a.as
  multiply := fun {_ _ _} => D.mult
  left := fun {_ _} => (ops D).left
  right := fun {_ _} => (ops D).right
  assoc := fun {_ _ _ _} => (ops D).assoc
theorem sourceLaws : Laws (sourceOps D) := by
  have L := RepresentableComparisonTriangle.laws D
  constructor
  · intro _ _ _ _ t; exact L.leftNat t
  · intro _ _ _ _ t; exact L.rightNat t
  · intro _ _ _ _ _ _ t g h; exact L.assocFirst t g h
  · intro _ _ _ _ f _ _ t h; exact L.assocMiddle f t h
  · intro _ _ _ _ f g _ _ t; exact L.assocLast f g t
  · intro _ _ _ f g; exact L.triangle f g
  · intro _ _ _ _ _ f g h i; exact L.pentagon f g h i
instance sourceBicategory : Bicategory (Source D) :=
  build (sourceOps D) (sourceLaws D)
def oplax : (Source D) ⥤ᵒᵖᴸ B where
  obj a := a.as
  map f := X D f
  map₂ t := Y D t
  map₂_id f := (D.hom _ _).map_id f
  map₂_comp t s := (D.hom _ _).map_comp t s
  mapId a := (D.unitIso a.as).hom
  mapComp f g := (D.cmpIso f g).hom
  mapComp_naturality_left := by
    intro a b c f f' t g
    change Y D (W D t (𝟙 g)) ≫ (D.cmpIso f' g).hom = (D.cmpIso f g).hom ≫ Y D t ▷ X D g
    have h := D.cmpNat t (𝟙 g)
    simpa only [horizontal,Functor.map_id,whiskerLeft_id,Category.comp_id] using h
  mapComp_naturality_right := by
    intro a b c f g g' t
    change Y D (W D (𝟙 f) t) ≫ (D.cmpIso f g').hom = (D.cmpIso f g).hom ≫ X D f ◁ Y D t
    have h := D.cmpNat (𝟙 f) t
    simpa only [horizontal,Functor.map_id,id_whiskerRight,Category.id_comp] using h
  map₂_associator := by
    intro a b c d f g h
    change Y D ((ops D).assoc f g h).hom ≫ (D.cmpIso f (RepresentableComparisonTransport.cmp D g h)).hom ≫
        X D f ◁ (D.cmpIso g h).hom =
      (D.cmpIso (RepresentableComparisonTransport.cmp D f g) h).hom ≫
        (D.cmpIso f g).hom ▷ X D h ≫ (α_ (X D f) (X D g) (X D h)).hom
    have H := assocPort D f g h
    simp only [assocImage,Iso.trans_hom,Iso.symm_hom] at H
    have J : (tail D f g h).inv ≫ (D.cmpIso f (RepresentableComparisonTransport.cmp D g h)).hom ≫
        X D f ◁ (D.cmpIso g h).hom = 𝟙 _ := by
      change (tail D f g h).inv ≫ (tail D f g h).hom = _
      exact (tail D f g h).inv_hom_id
    rw [H]
    simp only [head,Iso.trans_hom,whiskerRightIso_hom,Category.assoc,J,Category.comp_id]
  map₂_leftUnitor := by
    intro a b f
    exact leftPort D f
  map₂_rightUnitor := by
    intro a b f
    exact rightPort D f
def pseudo : (Source D) ⥤ᵖ B :=
  Pseudofunctor.mkOfOplax (oplax D) {
    mapIdIso a := D.unitIso a.as
    mapCompIso f g := D.cmpIso f g
    mapIdIso_hom := fun {_} => rfl
    mapCompIso_hom _ _ := rfl }
theorem onto : Function.Surjective (pseudo D).obj := fun b => ⟨⟨b,rfl⟩,rfl⟩
end ContextualComposition.GrothendieckStep.RepresentableComparisonPseudofunctor
