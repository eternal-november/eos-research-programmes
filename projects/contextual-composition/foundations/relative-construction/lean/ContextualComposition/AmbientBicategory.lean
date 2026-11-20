module
public import ContextualComposition.AmbientWhiskering
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientBicategory
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite FibreValue TelescopeSquares
open ContextadAmbientPayload AmbientModificationAction AmbientBlockCells AmbientRoundTrip AmbientCellFunctor AmbientWhiskering AmbientBlockIteration
open CategoryTheory.Bicategory
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
universe u v
variable (B : Type u) [Category.{max u v} B]
abbrev Obj := InducedBicategory _ (fun Q : PackedCuts.Psh.{u,max u v,u,v} B => Q.toPseudofunctor')
variable {B}
abbrev underlying (Q : Obj.{u,v} B) : PackedCuts.Psh.{u,max u v,u,v} B := Q
variable {X Y Z W : Obj.{u,v} B}
local instance instHom {L : Type*} [Bicategory L] {M : Type*} [Bicategory M] (F G : Pseudofunctor L M) : Category (StrongTrans F G) := StrongTrans.homCategory
theorem idComp (f : X ⟶ Y) : 𝟙 X ≫ f = f := by
  apply InducedBicategory.hom_ext; apply encodeInjective
  change totalStrong (StrongTrans.vcomp (𝟙 (underlying X).toPseudofunctor') f.hom) = totalStrong f.hom
  rw [strongComp,strongId,Functor.id_comp]
theorem compId (f : X ⟶ Y) : f ≫ 𝟙 Y = f := by
  apply InducedBicategory.hom_ext; apply encodeInjective
  change totalStrong (f.hom.vcomp (𝟙 (underlying Y).toPseudofunctor')) = totalStrong f.hom
  rw [strongComp,strongId,Functor.comp_id]
theorem compAssoc (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) : (f ≫ g) ≫ h = f ≫ g ≫ h := by
  apply InducedBicategory.hom_ext; apply encodeInjective
  change totalStrong ((f.hom.vcomp g.hom).vcomp h.hom) = totalStrong (f.hom.vcomp (g.hom.vcomp h.hom))
  simp only [strongComp,Functor.assoc]
def component {f g : X ⟶ Y} (k : f ⟶ g) (A : B) (x : (underlying X).obj (op A)) := (k.hom.as.app ⟨op A⟩).toNatTrans.app x
theorem componentCast {f g : X ⟶ Y} (h : f = g) (A : B) (x : (underlying X).obj (op A)) :
    Pure (component (eqToHom h) A x) := by subst g; exact pureId _
theorem pureIso {f g : X ⟶ Y} (e : f ≅ g) (h : f = g) (q : ∀ A x, Pure (component e.hom A x)) : e = eqToIso h := by
  apply Iso.ext
  apply InducedBicategory.hom₂_ext; apply StrongTrans.Hom.ext; apply StrongTrans.Modification.ext
  funext A; apply Cat.Hom₂.ext; ext x : 2
  exact pureEq (q A.as.unop x) (componentCast h A.as.unop x)
instance strict : Bicategory.Strict (Obj.{u,v} B) where
  id_comp := idComp
  comp_id := compId
  assoc := compAssoc
  leftUnitor_eqToIso _f := pureIso _ _ (fun _ _ => pureId _)
  rightUnitor_eqToIso _f := pureIso _ _ (fun _ _ => pureId _)
  associator_eqToIso _f _g _h := pureIso _ _ (fun _ _ => pureId _)
variable {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split)
abbrev obj (n : Nat) (Q : Obj.{u,v} B) : Obj.{u,v} B := PackedFree.pow S (underlying Q) n
noncomputable abbrev map (n : Nat) (f : X ⟶ Y) : obj S n X ⟶ obj S n Y := InducedBicategory.mkHom (blockStrong (S := S) f.hom n)
noncomputable abbrev cell (n : Nat) {f g : X ⟶ Y} (m : f ⟶ g) : map S n f ⟶ map S n g := InducedBicategory.mkHom₂ (mapCell S n m.hom)
theorem comp (n : Nat) (f : X ⟶ Y) (g : Y ⟶ Z) : map S n (f ≫ g) = map S n f ≫ map S n g := InducedBicategory.hom_ext (blockComp S f.hom g.hom n)
theorem homCast {f g : X ⟶ Y} (h : f = g) : (eqToHom h).hom = eqToHom (congrArg InducedBicategory.Hom.hom h) := by subst g; rfl
noncomputable def action (n : Nat) : StrictPseudofunctor (Obj.{u,v} B) (Obj.{u,v} B) :=
  StrictPseudofunctor.mk'' {
    obj := obj S n
    map := map S n
    map₂ := cell S n
    map_id X := InducedBicategory.hom_ext (blockId S (underlying X) n)
    map_comp := comp S n
    map₂_id f := InducedBicategory.hom₂_ext (StrongTrans.Hom.ext (blockModId S f.hom n))
    map₂_comp t q := InducedBicategory.hom₂_ext (StrongTrans.Hom.ext (blockModComp S t.hom.as q.hom.as n))
    map₂_whisker_left := by
      intro X Y Z f g g' t
      apply InducedBicategory.hom₂_ext; simp only [InducedBicategory.Hom.category_comp_hom,homCast]; exact mapLeft S n f.hom t.hom
    map₂_whisker_right t f := by
      apply InducedBicategory.hom₂_ext; simp only [InducedBicategory.Hom.category_comp_hom,homCast]; exact mapRight S n t.hom f.hom }
end ContextualComposition.GrothendieckStep.AmbientBicategory
