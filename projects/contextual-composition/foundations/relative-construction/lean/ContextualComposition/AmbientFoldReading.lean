module
public import ContextualComposition.AmbientFoldFrames
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientFoldReading
open CategoryTheory CategoryTheory.Functor CategoryTheory.Bicategory TelescopeSquares
open AmbientBicategory AmbientCoordinates AmbientHorizontalDiagrams AmbientFoldFrames
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
universe u v
section Generic
variable {C : Type*} [Bicategory C] (F : StrictPseudofunctor C C)
variable {x y z w : C} {p : x ⟶ y} {q : y ⟶ z} {t : x ⟶ w} {n : w ⟶ z} {r : x ⟶ z}
theorem framedInv (e : p ≫ q = r) (s : r ≅ t ≫ n) :
    (foldMap F (eqToIso e ≪≫ s)).inv =
      eqToHom (F.map_comp t n).symm ≫ F.map₂ s.inv ≫ eqToHom ((congrArg F.map e.symm).trans (F.map_comp p q)) := by
  subst r
  simp [mapInv]
end Generic
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable {X Y : Obj.{u,v} B} {i j : Nat} {a b c d : obj S i X ⟶ obj S j Y}
theorem stays {z : b ⟶ c} (e : a = b) (h : c = d) (x : Raw S X i) :
    Aligned (atRaw S (eqToHom e ≫ z ≫ eqToHom h) x) (atRaw S z x) := by
  subst a; subst d; simpa using Aligned.refl (atRaw S z x)
end ContextualComposition.GrothendieckStep.AmbientFoldReading
