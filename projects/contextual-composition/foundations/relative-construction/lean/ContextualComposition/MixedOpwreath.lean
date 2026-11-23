module
public import Mathlib.CategoryTheory.Monad.Kleisli

/-! Street's mixed opwreath in Cat. The seven component laws present a comonad on the Kleisli category of T. No comonad on the base endofunctor G is supplied. -/

@[expose] public section
namespace ContextualComposition.MixedOpwreath
open CategoryTheory
set_option backward.isDefEq.respectTransparency false

universe u v
variable {C : Type u} [Category.{v} C] (T : Monad C) (G : C ⥤ C)

abbrev kl (X : C) := Kleisli.mk T X
abbrev J := Kleisli.Adjunction.toKleisli T

abbrev asHom {X Y : C} (f : X ⟶ T.obj Y) : kl T X ⟶ kl T Y := Kleisli.Hom.mk f

/-- The generating Kleisli arrow with underlying identity on T X. -/
def generic (X : C) : kl T (T.obj X) ⟶ kl T X := ⟨𝟙 _⟩

theorem pure_then {X Y Z : C} (p : X ⟶ Y) (h : kl T Y ⟶ kl T Z) :
    ((J T).map p ≫ h).of = p ≫ h.of := by
  change (p ≫ T.η.app Y) ≫ T.map h.of ≫ T.μ.app Z = _
  rw [Category.assoc, ← T.η.naturality_assoc h.of]
  simp

theorem then_pure {X Y Z : C} (h : kl T X ⟶ kl T Y) (p : Y ⟶ Z) :
    (h ≫ (J T).map p).of = h.of ≫ T.map p := by
  change h.of ≫ T.map (p ≫ T.η.app Z) ≫ T.μ.app Z = _
  simp

theorem factor {X Y : Kleisli T} (f : X ⟶ Y) : (J T).map f.of ≫ generic T Y.of = f := by
  apply Kleisli.hom_ext
  rw [pure_then]
  exact Category.comp_id _

/-- Naturality on all Kleisli arrows follows from the pure arrows and the generic arrows. -/
theorem natural_of_generators (F H : Kleisli T ⥤ Kleisli T)
    (a : ∀ X, F.obj X ⟶ H.obj X)
    (onPure : ∀ {X Y : C} (p : X ⟶ Y), F.map ((J T).map p) ≫ a _ = a _ ≫ H.map ((J T).map p))
    (onGeneric : ∀ Y, F.map (generic T Y) ≫ a _ = a _ ≫ H.map (generic T Y))
    {X Y} (f : X ⟶ Y) : F.map f ≫ a _ = a _ ≫ H.map f := by
  rw [← factor T f, F.map_comp, H.map_comp, Category.assoc, onGeneric, ← Category.assoc]
  erw [onPure f.of, Category.assoc]
  rfl

structure Crossing where
  ζ : T.toFunctor ⋙ G ⟶ G ⋙ T.toFunctor
  unit : ∀ X, G.map (T.η.app X) ≫ ζ.app X = T.η.app (G.obj X)
  mult : ∀ X, G.map (T.μ.app X) ≫ ζ.app X =
    ζ.app (T.obj X) ≫ T.map (ζ.app X) ≫ T.μ.app (G.obj X)

variable {T G}

def Crossing.lift (z : Crossing T G) : Kleisli T ⥤ Kleisli T where
  obj X := kl T (G.obj X.of)
  map f := ⟨G.map f.of ≫ z.ζ.app _⟩
  map_id X := Kleisli.hom_ext (z.unit X.of)
  map_comp {X Y Z} f g := by
    apply Kleisli.hom_ext
    change G.map (f.of ≫ T.map g.of ≫ T.μ.app _) ≫ z.ζ.app _ =
      (G.map f.of ≫ z.ζ.app _) ≫ T.map (G.map g.of ≫ z.ζ.app _) ≫ T.μ.app _
    have nat : G.map (T.map g.of) ≫ z.ζ.app _ = z.ζ.app _ ≫ T.map (G.map g.of) :=
      z.ζ.naturality g.of
    simp only [Functor.map_comp, Category.assoc, z.mult]
    rw [← Category.assoc (G.map (T.map g.of)), nat, Category.assoc]

theorem Crossing.lift_pure (z : Crossing T G) {X Y : C} (p : X ⟶ Y) :
    z.lift.map ((J T).map p) = (J T).map (G.map p) := by
  apply Kleisli.hom_ext
  change G.map (p ≫ T.η.app Y) ≫ z.ζ.app Y = G.map p ≫ T.η.app _
  rw [Functor.map_comp, Category.assoc, z.unit]

abbrev deltaAt (d : G ⟶ (G ⋙ G) ⋙ T.toFunctor) (X : C) :
    kl T (G.obj X) ⟶ kl T (G.obj (G.obj X)) := asHom T (d.app X)

abbrev counitAt (e : G ⟶ T.toFunctor) (X : C) : kl T (G.obj X) ⟶ kl T X :=
  asHom T (e.app X)

variable (T G)

/-- Compatibility of d and e on the generic Kleisli arrows, followed by coassociativity and both counit laws. Together with Crossing.unit and Crossing.mult these are the seven opwreath laws. -/
structure Data extends Crossing T G where
  d : G ⟶ (G ⋙ G) ⋙ T.toFunctor
  e : G ⟶ T.toFunctor
  d_generic : ∀ X, toCrossing.lift.map (generic T X) ≫ deltaAt d X =
    deltaAt d (T.obj X) ≫ toCrossing.lift.map (toCrossing.lift.map (generic T X))
  e_generic : ∀ X, toCrossing.lift.map (generic T X) ≫ counitAt e X =
    counitAt e (T.obj X) ≫ generic T X
  coassoc : ∀ X, deltaAt d X ≫ toCrossing.lift.map (deltaAt d X) = deltaAt d X ≫ deltaAt d (G.obj X)
  left_counit : ∀ X, deltaAt d X ≫ counitAt e (G.obj X) = 𝟙 (kl T (G.obj X))
  right_counit : ∀ X, deltaAt d X ≫ toCrossing.lift.map (counitAt e X) = 𝟙 (kl T (G.obj X))

variable {T G} (D : Data T G)

def liftedComonad : Comonad (Kleisli T) where
  toFunctor := D.toCrossing.lift
  ε := {
    app := fun X => ⟨D.e.app X.of⟩
    naturality := by
      apply natural_of_generators T
      · intro X Y p
        rw [D.toCrossing.lift_pure]
        apply Kleisli.hom_ext
        rw [pure_then]
        change _ = ((⟨D.e.app X⟩ : kl T (G.obj X) ⟶ kl T X) ≫ (J T).map p).of
        rw [then_pure]
        exact D.e.naturality p
      · exact D.e_generic }
  δ := {
    app := fun X => ⟨D.d.app X.of⟩
    naturality := by
      apply natural_of_generators T
      · intro X Y p
        simp only [Functor.comp_map, D.toCrossing.lift_pure]
        apply Kleisli.hom_ext
        rw [pure_then, then_pure]
        exact D.d.naturality p
      · exact D.d_generic }
  coassoc X := D.coassoc X.of
  left_counit X := D.left_counit X.of
  right_counit X := D.right_counit X.of

/-- The mixed category is the co-Kleisli category of the lifted comonad. -/
abbrev Mixed := Cokleisli (liftedComonad D)

def pureFunctor : C ⥤ Mixed D :=
  J T ⋙ Cokleisli.Adjunction.toCokleisli (liftedComonad D)

def homEquiv (X Y : C) : ((pureFunctor D).obj X ⟶ (pureFunctor D).obj Y) ≃ (G.obj X ⟶ T.obj Y) where
  toFun f := f.of.of
  invFun f := ⟨⟨f⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem identity (X : C) : homEquiv D X X (𝟙 _) = D.e.app X := rfl

theorem pure_eq {X Y : C} (p : X ⟶ Y) :
    homEquiv D X Y ((pureFunctor D).map p) = D.e.app X ≫ T.map p := by
  exact then_pure T (⟨D.e.app X⟩ : kl T (G.obj X) ⟶ kl T X) p

theorem pure_eq_other {X Y : C} (p : X ⟶ Y) :
    homEquiv D X Y ((pureFunctor D).map p) = G.map p ≫ D.e.app Y := by
  rw [pure_eq, D.e.naturality]

theorem convolution {X Y Z : C} (f : G.obj X ⟶ T.obj Y) (g : G.obj Y ⟶ T.obj Z) :
    homEquiv D X Z ((homEquiv D X Y).symm f ≫ (homEquiv D Y Z).symm g) =
    D.d.app X ≫ T.map (G.map f) ≫ T.map (D.ζ.app Y) ≫ T.map (T.map g) ≫ T.μ.app (T.obj Z) ≫ T.μ.app Z := by
  change D.d.app X ≫ T.map ((G.map f ≫ D.ζ.app Y) ≫ T.map g ≫ T.μ.app Z) ≫ T.μ.app Z = _
  simp only [Functor.map_comp, Category.assoc, Monad.assoc]

end ContextualComposition.MixedOpwreath
