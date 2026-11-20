module
public import ContextualComposition.RepresentableKleisliConstraints
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableStrictFold
open CategoryTheory CategoryTheory.Bicategory
open scoped CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
section Cast
variable {C : Type*} [Bicategory C] {a b c d : C}
theorem castLeft (f : a ⟶ b) {s t : b ⟶ c} (e : s = t) :
    whiskerLeftIso f (eqToIso e) = eqToIso (congrArg (f ≫ ·) e) := by subst t; apply Iso.ext; simp
theorem castRight {f g : a ⟶ b} (e : f = g) (s : b ⟶ c) :
    whiskerRightIso (eqToIso e) s = eqToIso (congrArg (· ≫ s) e) := by subst g; apply Iso.ext; simp
theorem castIsoComp {D : Type*} [Category D] {x y z : D} (e : x = y) (w : y = z) :
    eqToIso e ≪≫ eqToIso w = eqToIso (e.trans w) := by subst y; subst z; simp
end Cast
section Expand
variable {C : Type*} [Bicategory C] (F : StrictPseudofunctor C C) {a b c d : C}
variable (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d)
def unfoldThree :=
  F.mapComp (f ≫ g) h ≪≫ whiskerRightIso (F.mapComp f g) (F.map h)
theorem castThree (e : F.map ((f ≫ g) ≫ h) = (F.map f ≫ F.map g) ≫ F.map h) :
    unfoldThree F f g h = eqToIso e := by
  unfold unfoldThree
  rw [F.mapComp_eq_eqToIso,F.mapComp_eq_eqToIso,castRight,castIsoComp]
end Expand
end ContextualComposition.GrothendieckStep.RepresentableStrictFold
