module
public import ContextualComposition.RepresentableKleisliFunctor
public import Mathlib.CategoryTheory.Products.Basic
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableNativeComposition
open CategoryTheory CategoryTheory.Functor Opposite CategoryTheory.Bicategory
open AmbientBicategory AmbientCoherentPseudomonad RepresentableKleisli
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 850000
universe u
variable {B : Type u} [Category.{u} B] {P : Endpoints.{u,u,u,u} B} {S : P.Split}
variable {A D E : B} (T : Data S)
def rows (A D : B) := (fibreEquiv (S := S) (A := A) (D := D)).functor
def lift (A D : B) := (fibreEquiv (S := S) (A := A) (D := D)).inverse
theorem canonicalEval (x : Row (P := P) A D) : row (canonical (S := S) x) = x :=
  RepresentableYoneda.unit (underlying.{u,u} (KObj S D)) A x
noncomputable def native : Row (P := P) A D × Row (P := P) D E ⥤ Row (P := P) A E :=
  (lift (S := S) A D).prod (lift (S := S) D E) ⋙ composeFunctor T ⋙ rows (S := S) A E
theorem nativeObject (x : Row (P := P) A D) (y : Row (P := P) D E) :
    (native T).obj (x,y) = result T x y :=
  (actualAt T (canonical (S := S) x) y).trans (congrArg (result T · y) (canonicalEval x))
def units : 𝟭 (KH S A D × KH S D E) ≅
    ((rows (S := S) A D).prod (rows (S := S) D E)) ⋙ ((lift (S := S) A D).prod (lift (S := S) D E)) :=
  NatIso.prod (fibreEquiv (S := S) (A := A) (D := D)).unitIso (fibreEquiv (S := S) (A := D) (D := E)).unitIso
def transport {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (p : C ⥤ D) (l : D ⥤ C) (h : C ⥤ E) (η : 𝟭 C ≅ p ⋙ l) : h ≅ p ⋙ l ⋙ h :=
  eqToIso (Functor.id_comp h).symm ≪≫ isoWhiskerRight η h ≪≫ eqToIso (Functor.assoc p l h)
noncomputable def comparison :
    composeFunctor T ⋙ rows (S := S) A E ≅
      ((rows (S := S) A D).prod (rows (S := S) D E)) ⋙ native T :=
  transport ((rows (S := S) A D).prod (rows (S := S) D E)) ((lift (S := S) A D).prod (lift (S := S) D E))
    (composeFunctor T ⋙ rows (S := S) A E) (units (S := S) (A := A) (D := D) (E := E))
theorem typePins (x : Row (P := P) A D) (y : Row (P := P) D E) :
    (lift (S := S) A D).obj x = canonical (S := S) x ∧ (lift (S := S) D E).obj y = canonical (S := S) y :=
  ⟨rfl,rfl⟩
noncomputable def atArbitrary (f : KH S A D) (g : KH S D E) :
    row (compose T f g) ≅ result T (row f) (row g) :=
  (comparison T).app (f,g) ≪≫ eqToIso (nativeObject T (row f) (row g))
end ContextualComposition.GrothendieckStep.RepresentableNativeComposition
