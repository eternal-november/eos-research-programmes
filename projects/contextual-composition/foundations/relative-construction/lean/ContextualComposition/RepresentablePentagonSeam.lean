module
public import ContextualComposition.RepresentableKleisliPentagonPaths
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentablePentagonSeam
open CategoryTheory CategoryTheory.Bicategory
open scoped CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
section
variable {C : Type*} [Bicategory C]
@[reassoc]
theorem prefixCast {a b c d : C} (f : a ⟶ b) {p q : b ⟶ c} (e : p = q)
    {s t : c ⟶ d} (x : s ⟶ t) {U V : a ⟶ d}
    (P : U = f ≫ (p ≫ s)) (Q : f ≫ (p ≫ t) = V) :
    eqToHom P ≫ f ◁ p ◁ x ≫ eqToHom Q =
    eqToHom (P.trans (congrArg (fun k => f ≫ (k ≫ s)) e)) ≫ f ◁ q ◁ x ≫
      eqToHom ((congrArg (fun k => f ≫ (k ≫ t)) e).symm.trans Q) := by
  subst q
  rfl
@[reassoc]
theorem suffixCast {a b c d : C} (f : a ⟶ b) {p q : c ⟶ d} (e : p = q)
    {s t : b ⟶ c} (x : s ⟶ t) {U V : a ⟶ d}
    (P : U = f ≫ (s ≫ p)) (Q : f ≫ (t ≫ p) = V) :
    eqToHom P ≫ f ◁ (x ▷ p) ≫ eqToHom Q =
    eqToHom (P.trans (congrArg (fun k => f ≫ (s ≫ k)) e)) ≫ f ◁ (x ▷ q) ≫
      eqToHom ((congrArg (fun k => f ≫ (t ≫ k)) e).symm.trans Q) := by
  subst q
  rfl
@[reassoc]
theorem prefixCast₂ {a b c d e : C} (f : a ⟶ b) (g : b ⟶ c) {p q : c ⟶ d} (h : p = q)
    {s t : d ⟶ e} (x : s ⟶ t) {U V : a ⟶ e}
    (P : U = f ≫ (g ≫ (p ≫ s))) (Q : f ≫ (g ≫ (p ≫ t)) = V) :
    eqToHom P ≫ f ◁ g ◁ p ◁ x ≫ eqToHom Q =
    eqToHom (P.trans (congrArg (fun k => f ≫ (g ≫ (k ≫ s))) h)) ≫ f ◁ g ◁ q ◁ x ≫
      eqToHom ((congrArg (fun k => f ≫ (g ≫ (k ≫ t))) h).symm.trans Q) := by
  subst q
  rfl
end
end ContextualComposition.GrothendieckStep.RepresentablePentagonSeam
