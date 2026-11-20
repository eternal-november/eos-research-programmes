module
public import ContextualComposition.AmbientOperationLaws
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientPseudonaturality
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite FibreValue TelescopeSquares
open AmbientBicategory AmbientCoordinates ContextadModification NativeBlocks CategoryTheory.Bicategory
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
universe u v
section General
variable {C D : Type*} [Bicategory C] [Bicategory D] [Bicategory.Strict D] (F G : StrictPseudofunctor C D)
variable (c : ∀ X, F.obj X ⟶ G.obj X) (s : ∀ {X Y} (f : X ⟶ Y), F.map f ≫ c Y ≅ c X ≫ G.map f)
theorem unitFrame (X : C) : F.map (𝟙 X) ≫ c X = c X ≫ G.map (𝟙 X) := by rw [F.map_id,G.map_id,Category.id_comp,Category.comp_id]
theorem frame₀ {X Y Z : C} (a : X ⟶ Y) (b : Y ⟶ Z) : F.map (a ≫ b) ≫ c Z = F.map a ≫ (F.map b ≫ c Z) := by rw [F.map_comp,Category.assoc]
theorem frame₁ {X Y Z : C} (a : X ⟶ Y) (b : Y ⟶ Z) : F.map a ≫ (c Y ≫ G.map b) = (F.map a ≫ c Y) ≫ G.map b := (Category.assoc ..).symm
theorem frame₂ {X Y Z : C} (a : X ⟶ Y) (b : Y ⟶ Z) : (c X ≫ G.map a) ≫ G.map b = c X ≫ G.map (a ≫ b) := by rw [G.map_comp,Category.assoc]
def pasted {X Y Z : C} (a : X ⟶ Y) (b : Y ⟶ Z) :=
  eqToIso (frame₀ F G c a b) ≪≫ whiskerLeftIso (F.map a) (s b) ≪≫ eqToIso (frame₁ F G c a b) ≪≫ whiskerRightIso (s a) (G.map b) ≪≫ eqToIso (frame₂ F G c a b)
variable (m : ∀ {X Y} {a b : X ⟶ Y} (t : a ⟶ b), (s a).inv ≫ F.map₂ t ▷ c Y = c X ◁ G.map₂ t ≫ (s b).inv)
variable (i : ∀ X, s (𝟙 X) = eqToIso (unitFrame F G c X))
variable (k : ∀ {X Y Z : C} (a : X ⟶ Y) (b : Y ⟶ Z), s (a ≫ b) = pasted F G c s a b)
def assemble : StrongTrans F.toPseudofunctor G.toPseudofunctor where
  app := c
  naturality := s
  naturality_naturality {X Y} {a b} t := by
    apply (cancel_epi (s a).inv).mp
    rw [← Category.assoc,m t,Category.assoc,Iso.inv_hom_id,Category.comp_id,Iso.inv_hom_id_assoc]
  naturality_id X := by
    rw [i X,F.mapId_eq_eqToIso,G.mapId_eq_eqToIso,Strict.leftUnitor_eqToIso,Strict.rightUnitor_eqToIso]
    simp
  naturality_comp {X Y Z} a b := by
    rw [k a b,F.mapComp_eq_eqToIso,G.mapComp_eq_eqToIso]
    simp only [pasted,Iso.trans_hom,whiskerLeftIso_hom,whiskerRightIso_hom,Strict.associator_eqToIso,eqToIso.hom,eqToIso.inv,
      whiskerLeft_eqToHom,eqToHom_whiskerRight,Category.assoc,eqToHom_trans,eqToHom_trans_assoc]
end General
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split)
variable {i j : Nat} (r : ContextadRoutes.Map S i j) (p : gradeCart r)
noncomputable def operation :
    StrongTrans (action S i).toPseudofunctor (action S j).toPseudofunctor :=
  assemble (action S i) (action S j) (oper S r p) (fun f => comparison S r p f)
    (fun t => AmbientOperationLaws.modification S r p t)
    (fun X => AmbientOperationLaws.identity S r p X)
    (fun a b => AmbientOperationLaws.composition S r p a b)
end ContextualComposition.GrothendieckStep.AmbientPseudonaturality
