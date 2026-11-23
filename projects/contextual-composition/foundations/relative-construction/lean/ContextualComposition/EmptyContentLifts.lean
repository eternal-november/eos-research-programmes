module
public import ContextualComposition.EmptyContentEquivalence

/-! Preservation of the marked transport arrows. Cartesian universality uses full faithfulness of the transition along the base map; it requires neither an invertible extension body nor admission of the map out of the empty interface in a display class. -/

@[expose] public section
noncomputable section
namespace ContextualComposition.EmptyContentTransport
open CategoryTheory CategoryTheory.Bicategory ContextualComposition.Factorization.Endpoint.Indexed
set_option backward.isDefEq.respectTransparency false

universe u w v
variable (L : LocallyDiscrete (Type u) ⥤ᵖ Cat.{v,w})
variable {A B D : Type u} (f : A ⟶ B) (P : Fibre L A) (Q : Fibre L B)
variable (cell : (action L f).obj P ≅ Q)

def above : (outInclusion L A).obj P ⟶ (outInclusion L B).obj Q := ⟨f,cell.hom⟩

theorem opcartesian (g : B ⟶ D) (R : Fibre L D)
    (t : (outInclusion L A).obj P ⟶ (outInclusion L D).obj R) (hb : t.base = f ≫ g) :
    ∃! k : (action L g).obj Q ⟶ R,
      above L f P Q cell ≫ (⟨g,k⟩ : (outInclusion L B).obj Q ⟶ (outInclusion L D).obj R) = t := by
  obtain ⟨b,t⟩ := t
  change b = f ≫ g at hb
  subst b
  let c := (Cat.Hom.toNatIso (L.mapComp f.toLoc g.toLoc)).app P
  let j := (action L g).mapIso cell
  refine ⟨j.inv ≫ c.inv ≫ t,?_,?_⟩
  · apply Pseudofunctor.Grothendieck.Hom.ext
    case hfg₁ => rfl
    change eqToHom _ ≫ c.hom ≫ j.hom ≫ j.inv ≫ c.inv ≫ t = t
    simp
  · intro k h
    have eq := Pseudofunctor.Grothendieck.Hom.congr h
    change c.hom ≫ j.hom ≫ k = eqToHom _ ≫ t at eq
    simp only [eqToHom_refl,Category.id_comp] at eq
    rw [← eq]
    simp

theorem cartesian [ff : (action L f).Full] [faith : (action L f).Faithful] {X : Type u}
    (g : X ⟶ A) (R : Fibre L X) (t : (outInclusion L X).obj R ⟶ (outInclusion L B).obj Q)
    (hb : t.base = g ≫ f) : ∃! k : (action L g).obj R ⟶ P,
      (⟨g,k⟩ : (outInclusion L X).obj R ⟶ (outInclusion L A).obj P) ≫ above L f P Q cell = t := by
  obtain ⟨b,t⟩ := t
  change b = g ≫ f at hb
  subst b
  let c := (Cat.Hom.toNatIso (L.mapComp g.toLoc f.toLoc)).app R
  let k := (action L f).preimage (c.inv ≫ t ≫ cell.inv)
  refine ⟨k,?_,?_⟩
  · apply Pseudofunctor.Grothendieck.Hom.ext
    case hfg₁ => rfl
    change eqToHom _ ≫ c.hom ≫ (action L f).map k ≫ cell.hom = t
    simp [k]
  · intro l h
    have eq := Pseudofunctor.Grothendieck.Hom.congr h
    change c.hom ≫ (action L f).map l ≫ cell.hom = eqToHom _ ≫ t at eq
    simp only [eqToHom_refl,Category.id_comp] at eq
    apply (action L f).map_injective
    rw [show (action L f).map k = _ from (action L f).map_preimage _, ← eq]
    simp

def gradeIso {s t : Base L} (g : s.1 ⟶ t.1) (a : s.2 ≅ t.2) :
    (action L g).obj ((E L s.1).obj s.2) ≅ (E L t.1).obj t.2 :=
  (comparison L g).app s.2 ≪≫ (E L t.1).mapIso a

theorem send_iso_grade {s t : Base L} (g : s.1 ⟶ t.1) (a : s.2 ≅ t.2) :
    (constantize L).map (⟨g,a.hom⟩ : s ⟶ t) =
      above L g ((E L s.1).obj s.2) ((E L t.1).obj t.2) (gradeIso L g a) := rfl

end ContextualComposition.EmptyContentTransport
