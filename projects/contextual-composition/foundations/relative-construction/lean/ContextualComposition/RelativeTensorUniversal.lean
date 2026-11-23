module
public import ContextualComposition.RelativeTensorCocones

@[expose] public section
namespace ContextualComposition.RelativeTensor
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory
universe v u vF uF vG uG vD uD
variable {B : Type u} [Category.{v} B]
variable {F : LocallyDiscrete B ⥤ᵖ Cat.{vF,uF}} {G : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vG,uG}}
variable {D : Type uD} [Category.{vD} D]
set_option backward.isDefEq.respectTransparency false

/-- Cocone transformations are defined by their fibre transformations and the positive balance squares. -/
@[ext] structure Transformation (S T : Cocone F G D) where
  components (i : B) : S.fiber i ⟶ T.fiber i
  square {i j : B} (u : i ⟶ j) (x : F.obj ⟨i⟩) (y : G.obj ⟨op j⟩) :
    (S.bal u x y).hom ≫ (components j).app ((forward F u).obj x,y) =
      (components i).app (x,(backward G u).obj y) ≫ (T.bal u x y).hom

instance coconeCategory : Category (Cocone F G D) where
  Hom := Transformation
  id _ := ⟨fun _ => 𝟙 _, by intros; simp⟩
  comp a b := ⟨fun i => a.components i ≫ b.components i,by
    intro i j u x y
    simp only [NatTrans.comp_app, ← Category.assoc, a.square]
    simp only [Category.assoc, b.square]⟩
  id_comp a := by apply Transformation.ext; funext i; exact Category.id_comp _
  comp_id a := by apply Transformation.ext; funext i; exact Category.comp_id _
  assoc a b c := by apply Transformation.ext; funext i; exact Category.assoc _ _ _

namespace Transformation
variable {S T : Cocone F G D} (a : Transformation S T)
abbrev atVertex (x : Vertex F G) := (a.components x.mid).app (x.first,x.second)

theorem at_edge {x y : Vertex F G} (t : Edge F G x y) :
    S.graph.map t ≫ a.atVertex y = a.atVertex x ≫ T.graph.map t := by
  cases t with
  | native f g => exact (a.components _).naturality (productMap f g)
  | balance u x y => exact a.square u x y
  | unbalance u x y =>
    change (S.bal u x y).inv ≫ _ = _ ≫ (T.bal u x y).inv
    apply (cancel_epi (S.bal u x y).hom).mp
    rw [Iso.hom_inv_id_assoc, ← Category.assoc, a.square, Category.assoc, Iso.hom_inv_id, Category.comp_id]

def extend : S.extend ⟶ T.extend :=
  CategoryTheory.Quotient.natTransLift (Relations F G) {
    app := fun x => a.atVertex x
    naturality := by
      intro x y f
      change (Paths.lift S.graph).map f ≫ a.atVertex y = a.atVertex x ≫ (Paths.lift T.graph).map f
      induction f with
      | nil => simp only [Paths.lift_nil]; erw [Category.id_comp, Category.comp_id]
      | cons p t h =>
        simp only [Paths.lift_cons, Category.assoc, a.at_edge]
        rw [← Category.assoc, h, Category.assoc] }

end Transformation

def extendFunctor : Cocone F G D ⥤ (Tensor F G ⥤ D) where
  obj S := S.extend
  map a := Transformation.extend a
  map_id _ := rfl
  map_comp _ _ := rfl

def restrictFunctor : (Tensor F G ⥤ D) ⥤ Cocone F G D where
  obj H := restrict H
  map a := ⟨fun i => Functor.whiskerLeft (insertion F G i) a,
    fun u x y => a.naturality (balancing F G u x y).hom⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def sectionFiber (S : Cocone F G D) (i : B) : (restrict S.extend).fiber i ≅ S.fiber i :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro x y f
    change S.extend.map ((quotient F G).map (nativePath F G f.1 f.2)) ≫ 𝟙 _ = 𝟙 _ ≫ _
    rw [S.extend_generator, Category.comp_id, Category.id_comp]; rfl)

def coconeSection (S : Cocone F G D) : restrict S.extend ≅ S where
  hom := ⟨fun i => (sectionFiber S i).hom, by
    intro i j u x y
    change S.extend.map ((quotient F G).map (balancePath F G u x y)) ≫ 𝟙 _ = 𝟙 _ ≫ _
    rw [S.extend_generator, Category.comp_id, Category.id_comp]; rfl⟩
  inv := ⟨fun i => (sectionFiber S i).inv, by
    intro i j u x y
    change _ ≫ 𝟙 _ = 𝟙 _ ≫ S.extend.map ((quotient F G).map (balancePath F G u x y))
    rw [S.extend_generator, Category.comp_id, Category.id_comp]; rfl⟩
  hom_inv_id := by apply Transformation.ext; funext i; exact (sectionFiber S i).hom_inv_id
  inv_hom_id := by apply Transformation.ext; funext i; exact (sectionFiber S i).inv_hom_id

def functorSection (H : Tensor F G ⥤ D) : (restrict H).extend ≅ H :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro x y f
    simp only [Iso.refl_hom,Category.comp_id,Category.id_comp]
    have h := Functor.congr_hom (extend_restrict H) f
    simpa using h)

/-- The pseudocoend represents independently specified pseudobalanced cocones and their compatible transformations at every target category. -/
def universalProperty : (Tensor F G ⥤ D) ≌ Cocone F G D :=
  CategoryTheory.Equivalence.mk restrictFunctor extendFunctor
    (NatIso.ofComponents (fun H => (functorSection H).symm) (by
      intro H K a
      apply NatTrans.ext; funext s
      change a.app s ≫ 𝟙 _ = 𝟙 _ ≫ a.app s
      simp))
    (NatIso.ofComponents coconeSection (by
      intro S T a
      apply Transformation.ext; funext i; apply NatTrans.ext; funext x
      change (a.components i).app x ≫ 𝟙 _ = 𝟙 _ ≫ (a.components i).app x
      simp))

end ContextualComposition.RelativeTensor
