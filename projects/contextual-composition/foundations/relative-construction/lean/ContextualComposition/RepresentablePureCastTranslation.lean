module
public import ContextualComposition.RepresentableStrictFold
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentablePureCastTranslation
open CategoryTheory CategoryTheory.Bicategory
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000


section Translate
variable {D : Type*} [Category D] {a b c d e f : D}

theorem association (s : a ≅ b) (l : b ≅ c) (k : c ≅ f)
    (r : a ≅ d) (j : d ≅ e) (q : e ≅ f) (cast : e = f)
    (l' : b ⟶ c) (r' : a ⟶ d)
    (hl : l.hom = l') (hr : r.hom = r') (hq : q = eqToIso cast)
    (law : s ≪≫ l ≪≫ k = r ≪≫ j ≪≫ q) :
    s.hom ≫ l' ≫ k.hom = r' ≫ j.hom ≫ eqToHom cast := by
  subst l'; subst r'; subst q
  exact congrArg Iso.hom law

theorem unital (s : a ≅ b) (q : b ≅ c) (r : a ≅ d) (k : d ≅ c)
    (cast : b = c) (r' : a ⟶ d) (hr : r.hom = r') (hq : q = eqToIso cast)
    (law : s ≪≫ q = r ≪≫ k) :
    s.hom ≫ eqToHom cast = r' ≫ k.hom := by
  subst r'; subst q
  exact congrArg Iso.hom law
end Translate

section Strict
universe x y z
variable {C : Type x} [Bicategory.{z,y} C] [Bicategory.Strict C] {a b c d e : C}

theorem assocTail (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (p : d ⟶ e) :
    whiskerRightIso (α_ f g h) p = eqToIso (congrArg (· ≫ p) (Category.assoc f g h)) :=
  (congrArg (fun q => whiskerRightIso q p) (Strict.associator_eqToIso f g h)).trans
    (RepresentableStrictFold.castRight (Category.assoc f g h) p)


theorem leftTail (f : a ⟶ b) (p : b ⟶ c) :
    whiskerRightIso (λ_ f) p = eqToIso (congrArg (· ≫ p) (Category.id_comp f)) :=
  (congrArg (fun q => whiskerRightIso q p) (Strict.leftUnitor_eqToIso f)).trans
    (RepresentableStrictFold.castRight (Category.id_comp f) p)

theorem rightTail (f : a ⟶ b) (p : b ⟶ c) :
    whiskerRightIso (ρ_ f) p = eqToIso (congrArg (· ≫ p) (Category.comp_id f)) :=
  (congrArg (fun q => whiskerRightIso q p) (Strict.rightUnitor_eqToIso f)).trans
    (RepresentableStrictFold.castRight (Category.comp_id f) p)
end Strict

end ContextualComposition.GrothendieckStep.RepresentablePureCastTranslation
