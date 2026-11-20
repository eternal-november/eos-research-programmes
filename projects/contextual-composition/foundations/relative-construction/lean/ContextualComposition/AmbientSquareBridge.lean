module
public import ContextualComposition.AmbientHorizontalNaturality
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientSquareBridge
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite
open AmbientBicategory AmbientCoordinates ContextadModification NativeBlocks CategoryTheory.Bicategory
open ContextadRoutes ContextadNativeLaws ContextadOuterCharts AmbientHorizontalFrames AmbientHorizontalDiagrams AmbientHorizontalNaturality
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
universe u v
section General
variable {C : Type*} [Bicategory C] {x y x' y' : C} {a b : x ⟶ x'} {k : y ⟶ y'}
variable {p q p₀ q₀ : x ⟶ y} {p' q' p₀' q₀' : x' ⟶ y'}
def bend (e : a = b) (h : p = p₀) (h' : p' = p₀') (s : b ≫ p₀' ≅ p₀ ≫ k) : a ≫ p' ≅ p ≫ k :=
  eqToIso (congrArg₂ (· ≫ ·) e h') ≪≫ s ≪≫ eqToIso (congrArg (· ≫ k) h.symm)
def reframe (p : p = p₀) (q : q = q₀) (t : p₀ ≅ q₀) := eqToIso p ≪≫ t ≪≫ eqToIso q.symm
theorem transport (e : a = b) (h : p = p₀) (h' : p' = p₀') (j : q = q₀) (j' : q' = q₀')
    (s : b ≫ p₀' ≅ p₀ ≫ k) (t : b ≫ q₀' ≅ q₀ ≫ k) (m : p₀ ≅ q₀) (n : p₀' ≅ q₀')
    (z : Square s t m n) : Square (bend e h h' s) (bend e j j' t) (reframe h j m) (reframe h' j' n) := by
  subst b; subst p₀; subst p₀'; subst q₀; subst q₀'
  simpa [bend,reframe,Square] using z
end General
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable {X Y : Obj.{u,v} B} {i j : Nat} {r s : Map S i j}
variable (c : ContextadLawTransport.Cell r s) (p : gradeCart r) (q : gradeCart s) (f : X ⟶ Y)
theorem sourceSquare :
    Square (comparison S r p f) (comparison S s q f) (AmbientNativeModification.cmp c p q X) (AmbientNativeModification.cmp c p q Y) :=
  AmbientNativeModification.unbend _ _ _ _ (AmbientNativeModification.invSquare c p q f)
theorem viaNative {a : obj S i X ⟶ obj S i Y} (e : a = AmbientBicategory.map S i f)
    {u v : obj S i X ⟶ obj S j X} {u' v' : obj S i Y ⟶ obj S j Y}
    (h : u = oper S r p X) (h' : u' = oper S r p Y) (z : v = oper S s q X) (z' : v' = oper S s q Y)
    (l : a ≫ u' ≅ u ≫ AmbientBicategory.map S j f) (t : a ≫ v' ≅ v ≫ AmbientBicategory.map S j f)
    (readsLeft : l = bend e h h' (comparison S r p f)) (readsRight : t = bend e z z' (comparison S s q f)) :
    Square l t (reframe h z (AmbientNativeModification.cmp c p q X)) (reframe h' z' (AmbientNativeModification.cmp c p q Y)) := by
  rw [readsLeft,readsRight]
  exact transport e h h' z z' _ _ _ _ (sourceSquare c p q f)
end ContextualComposition.GrothendieckStep.AmbientSquareBridge
