module
public import ContextualComposition.FixedEffects
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Algebra.Group.Defs
@[expose] public section
namespace ContextualComposition.MixedRecovery
open CategoryTheory
universe v u
variable {C : Type u} [Category.{v} C]

/-- A supplied mixed distributive law G T → T G. No category laws for the
mixed arrows are assumed here: only the four structural compatibility squares. -/
structure Law (G : Comonad C) (T : Monad C) where
  trans : T.toFunctor ⋙ G.toFunctor ⟶ G.toFunctor ⋙ T.toFunctor
  unit (A : C) : G.map (T.η.app A) ≫ trans.app A = T.η.app (G.obj A)
  counit (A : C) : trans.app A ≫ T.map (G.ε.app A) = G.ε.app (T.obj A)
  mul (A : C) : G.map (T.μ.app A) ≫ trans.app A =
    trans.app (T.obj A) ≫ T.map (trans.app A) ≫ T.μ.app (G.obj A)
  comul (A : C) : G.δ.app (T.obj A) ≫ G.map (trans.app A) ≫ trans.app (G.obj A) =
    trans.app A ≫ T.map (G.δ.app A)

attribute [reassoc] Law.unit Law.counit Law.mul Law.comul
variable {G : Comonad C} {T : Monad C} (L : Law G T)
abbrev Arrow (A B : C) := G.obj A ⟶ T.obj B
abbrev comp {A B D : C} (f : Arrow (G:=G) (T:=T) A B)
    (g : Arrow (G:=G) (T:=T) B D) : Arrow (G:=G) (T:=T) A D :=
  G.δ.app A ≫ G.map f ≫ L.trans.app B ≫ T.map g ≫ T.μ.app D
abbrev pure {A B : C} (f : A ⟶ B) : Arrow (G:=G) (T:=T) A B :=
  G.ε.app A ≫ f ≫ T.η.app B

theorem comp_pure {A B D : C} (f : Arrow (G:=G) (T:=T) A B) (b : B ⟶ D) :
    comp L f (pure b) = f ≫ T.map b := by
  simp only [comp, pure, Functor.map_comp, Category.assoc]
  rw [T.right_unit]
  dsimp at *
  simp only [Category.comp_id]
  rw [L.counit_assoc]
  rw [G.ε.naturality_assoc f]
  simp

theorem pure_comp {A B D : C} (a : A ⟶ B) (g : Arrow (G:=G) (T:=T) B D) :
    comp L (pure a) g = G.map a ≫ g := by
  simp only [comp, pure, Functor.map_comp, Category.assoc]
  rw [L.unit_assoc, ← T.η.naturality_assoc g]
  simp

def Square {A B A' B' : C} (f : Arrow (G:=G) (T:=T) A B)
    (g : Arrow (G:=G) (T:=T) A' B') (a : A ⟶ A') (b : B ⟶ B') : Prop :=
  f ≫ T.map b = G.map a ≫ g

theorem square_iff_quintet {A B A' B' : C} (f : Arrow (G:=G) (T:=T) A B)
    (g : Arrow (G:=G) (T:=T) A' B') (a : A ⟶ A') (b : B ⟶ B') :
    Square f g a b ↔ comp L f (pure b) = comp L (pure a) g := by
  rw [comp_pure, pure_comp]; rfl
theorem assoc {A B D E : C} (f : Arrow (G:=G) (T:=T) A B)
    (g : Arrow (G:=G) (T:=T) B D) (h : Arrow (G:=G) (T:=T) D E) :
    comp L (comp L f g) h = comp L f (comp L g h) := by
  simp only [comp, Functor.map_comp, Category.assoc]
  rw [L.mul_assoc]
  rw [← T.μ.naturality_assoc h]
  dsimp
  rw [← T.assoc E]
  have hn : G.map (T.map g) ≫ L.trans.app (T.obj D) =
      L.trans.app (G.obj B) ≫ T.map (G.map g) := L.trans.naturality g
  rw [← Category.assoc (G.map (T.map g)), hn]
  simp only [Category.assoc]
  dsimp
  rw [← Category.assoc (G.δ.app A) (G.map (G.δ.app A)), G.coassoc]
  simp only [Category.assoc]
  have hd : G.map f ≫ G.δ.app (T.obj B) =
      G.δ.app (G.obj A) ≫ G.map (G.map f) := G.δ.naturality f
  rw [← Category.assoc (G.δ.app (G.obj A)), ← hd]
  simp only [Category.assoc]
  dsimp
  rw [L.comul_assoc]

theorem left_unit {A B : C} (f : Arrow (G:=G) (T:=T) A B) :
    comp L (pure (𝟙 A)) f = f := by rw [pure_comp]; simp

theorem right_unit {A B : C} (f : Arrow (G:=G) (T:=T) A B) :
    comp L f (pure (𝟙 B)) = f := by rw [comp_pure]; simp

theorem pure_comp_pure {A B D : C} (a : A ⟶ B) (b : B ⟶ D) :
    comp L (pure a) (pure b) = pure (a ≫ b) := by
  rw [comp_pure]
  simp only [pure, Category.assoc]
  rw [← T.η.naturality b]
  rfl

/-- Object wrapper equips the actual mixed arrows with the derived category laws. -/
structure Mixed (L : Law G T) where
  obj : C

instance category : Category (Mixed L) where
  Hom A B := Arrow (G:=G) (T:=T) A.obj B.obj
  id A := pure (𝟙 A.obj)
  comp f g := comp L f g
  id_comp f := left_unit L f
  comp_id f := right_unit L f
  assoc f g h := assoc L f g h

theorem vertical {A B A' B' A'' B'' : C}
    {f : Arrow (G:=G) (T:=T) A B} {g : Arrow (G:=G) (T:=T) A' B'}
    {h : Arrow (G:=G) (T:=T) A'' B''}
    {a : A ⟶ A'} {b : B ⟶ B'} {a' : A' ⟶ A''} {b' : B' ⟶ B''}
    (hf : Square f g a b) (hg : Square g h a' b') :
    Square f h (a ≫ a') (b ≫ b') := by
  dsimp [Square] at *
  rw [Functor.map_comp, ← Category.assoc, hf, Category.assoc, hg,
    Functor.map_comp, Category.assoc]

theorem horizontal {A B D A' B' D' : C}
    {f : Arrow (G:=G) (T:=T) A B} {g : Arrow (G:=G) (T:=T) B D}
    {f' : Arrow (G:=G) (T:=T) A' B'} {g' : Arrow (G:=G) (T:=T) B' D'}
    {a : A ⟶ A'} {b : B ⟶ B'} {d : D ⟶ D'}
    (hf : Square f f' a b) (hg : Square g g' b d) :
    Square (comp L f g) (comp L f' g') a d := by
  rw [square_iff_quintet L] at *
  rw [assoc, hg, ← assoc, hf, assoc]

abbrev fromComonad {A B : C} (f : G.obj A ⟶ B) : Arrow (G:=G) (T:=T) A B :=
  f ≫ T.η.app B
abbrev fromMonad {A B : C} (f : A ⟶ T.obj B) : Arrow (G:=G) (T:=T) A B :=
  G.ε.app A ≫ f

theorem fromComonad_comp {A B D : C} (f : G.obj A ⟶ B) (g : G.obj B ⟶ D) :
    comp L (fromComonad f) (fromComonad g) =
      fromComonad (ComonadRecovery.comp G f g) := by
  simp only [comp, fromComonad, ComonadRecovery.comp, Functor.map_comp, Category.assoc]
  rw [L.unit_assoc, ← T.η.naturality_assoc g]
  simp

theorem fromMonad_comp {A B D : C} (f : A ⟶ T.obj B) (g : B ⟶ T.obj D) :
    comp L (fromMonad f) (fromMonad g) = fromMonad (MonadRecovery.comp T f g) := by
  simp only [comp, fromMonad, MonadRecovery.comp, Functor.map_comp, Category.assoc]
  rw [L.counit_assoc]
  rw [G.ε.naturality_assoc f]
  simp

theorem fromComonad_pure {A B : C} (f : A ⟶ B) :
    fromComonad (T:=T) (ComonadRecovery.pure G f) = pure (T:=T) (G:=G) f := by
  simp only [fromComonad, ComonadRecovery.pure, pure, Category.assoc]

theorem fromMonad_pure {A B : C} (f : A ⟶ B) :
    fromMonad (G:=G) (MonadRecovery.pure T f) = pure (T:=T) (G:=G) f := rfl

theorem fromComonad_square {A B A' B' : C} {f : G.obj A ⟶ B} {g : G.obj A' ⟶ B'}
    {a : A ⟶ A'} {b : B ⟶ B'} (h : ComonadRecovery.Square G f g a b) :
    Square (fromComonad (T:=T) f) (fromComonad g) a b := by
  dsimp [Square, fromComonad, ComonadRecovery.Square] at *
  rw [Category.assoc, ← T.η.naturality b]
  dsimp
  rw [← Category.assoc, h, Category.assoc]

theorem fromMonad_square {A B A' B' : C} {f : A ⟶ T.obj B} {g : A' ⟶ T.obj B'}
    {a : A ⟶ A'} {b : B ⟶ B'} (h : MonadRecovery.Square T f g a b) :
    Square (fromMonad (G:=G) f) (fromMonad g) a b := by
  dsimp [Square, fromMonad, MonadRecovery.Square] at *
  rw [Category.assoc, h]
  have hn : G.map a ≫ G.ε.app A' = G.ε.app A ≫ a := G.ε.naturality a
  rw [← Category.assoc, ← hn, Category.assoc]

theorem fromComonad_injective {A B : C} [Mono (T.η.app B)] :
    Function.Injective (fromComonad (G:=G) (T:=T) (A:=A) (B:=B)) := by
  intro f g h
  exact (cancel_mono (T.η.app B)).mp h

theorem fromMonad_injective {A B : C} [Epi (G.ε.app A)] :
    Function.Injective (fromMonad (G:=G) (T:=T) (A:=A) (B:=B)) := by
  intro f g h
  exact (cancel_epi (G.ε.app A)).mp h

namespace ReaderWriter
variable (E W : Type u) [Monoid W]

def reader : Comonad (Type u) where
  obj A := E × A
  map f := TypeCat.ofHom (fun x => (x.1, f x.2))
  ε := { app := fun _ => TypeCat.ofHom Prod.snd }
  δ := { app := fun _ => TypeCat.ofHom (fun x => (x.1, x)) }

def writer : Monad (Type u) where
  obj A := W × A
  map f := TypeCat.ofHom (fun x => (x.1, f x.2))
  η := { app := fun _ => TypeCat.ofHom (fun a => (1, a)) }
  μ := { app := fun _ => TypeCat.ofHom (fun x => (x.1 * x.2.1, x.2.2)) }
  assoc A := by ext x <;> simp [mul_assoc]
  left_unit A := by ext x <;> simp
  right_unit A := by ext x <;> simp

/-- The source's actual reader/writer swap, valid for any monoid, not only a
commutative one. The four law fields are proved, not supplied as assumptions. -/
def law : Law (reader E) (writer W) where
  trans := { app := fun _ => TypeCat.ofHom (fun x => (x.2.1, (x.1, x.2.2))) }
  unit A := by rfl
  counit A := by rfl
  mul A := by rfl
  comul A := by rfl

theorem comp_apply {A B D : Type u}
    (f : Arrow (G:=reader E) (T:=writer W) A B)
    (g : Arrow (G:=reader E) (T:=writer W) B D) (x : E × A) :
    comp (law E W) f g x =
      ((f x).1 * (g (x.1, (f x).2)).1, (g (x.1, (f x).2)).2) := rfl

theorem pure_apply {A B : Type u} (f : A ⟶ B) (x : E × A) :
    pure (G:=reader E) (T:=writer W) f x = (1, f x.2) := rfl

/-- An empty environment makes the comparison from the writer source
nonfaithful. The generic injectivity theorem therefore needs its epi hypothesis. -/
theorem empty_environment_not_injective (W₀ : Type) [Monoid W₀] :
    ¬ Function.Injective (fromMonad (G:=reader Empty) (T:=writer W₀)
      (A:=Bool) (B:=Bool)) := by
  intro h
  let f : Bool ⟶ (writer W₀).obj Bool := TypeCat.ofHom (fun b => (1, b))
  let g : Bool ⟶ (writer W₀).obj Bool := TypeCat.ofHom (fun _ => (1, false))
  have he : fromMonad (G:=reader Empty) f = fromMonad (G:=reader Empty) g := by
    ext x
    exact Empty.elim x.1
  have hf := ConcreteCategory.congr_hom (h he) true
  have hc : true = false := congrArg Prod.snd hf
  cases hc

end ReaderWriter
end ContextualComposition.MixedRecovery
