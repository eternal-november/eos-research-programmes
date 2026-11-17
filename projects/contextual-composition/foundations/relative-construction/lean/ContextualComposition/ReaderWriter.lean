module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Logic.Equiv.Defs

@[expose] public section

/-! Concrete reader/writer transpositions, retaining pure endpoint-square equations.
The base here is Type; the general cartesian-closed-base theorem is not asserted. -/
namespace ContextualComposition
universe u
namespace Reader
variable {E A B D A' B' : Type u}
abbrev CoArrow (E A B : Type u) := E × A → B
abbrev Arrow (E A B : Type u) := A → E → B

def transpose : CoArrow E A B ≃ Arrow E A B where
  toFun f a e := f (e,a)
  invFun f p := f p.2 p.1
  left_inv _ := rfl
  right_inv _ := rfl

def coComp (f : CoArrow E A B) (g : CoArrow E B D) : CoArrow E A D :=
  fun p => g (p.1, f p)
def comp (f : Arrow E A B) (g : Arrow E B D) : Arrow E A D :=
  fun a e => g (f a e) e

theorem transpose_comp (f : CoArrow E A B) (g : CoArrow E B D) :
    transpose (coComp f g) = comp (transpose f) (transpose g) := rfl

theorem transpose_pure (f : A → B) :
    transpose (fun p : E × A => f p.2) = (fun a (_ : E) => f a) := rfl

def CoSquare (f : CoArrow E A B) (g : CoArrow E A' B') (a : A → A') (b : B → B') : Prop :=
  ∀ e x, b (f (e,x)) = g (e,a x)
def Square (f : Arrow E A B) (g : Arrow E A' B') (a : A → A') (b : B → B') : Prop :=
  ∀ x e, b (f x e) = g (a x) e

theorem square_iff (f : CoArrow E A B) (g : CoArrow E A' B') (a : A → A') (b : B → B') :
    CoSquare f g a b ↔ Square (transpose f) (transpose g) a b := by
  constructor <;> intro h x y <;> exact h y x
end Reader

namespace Writer
variable {W A B D A' B' D' : Type u} [Monoid W]
structure Graded (W A B : Type u) where
  grade : A → W
  body : A → B

def encode : Graded W A B ≃ (A → W × B) where
  toFun f a := (f.grade a, f.body a)
  invFun f := ⟨fun a => (f a).1, fun a => (f a).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def comp (f : Graded W A B) (g : Graded W B D) : Graded W A D :=
  ⟨fun a => f.grade a * g.grade (f.body a), fun a => g.body (f.body a)⟩
def pure (f : A → B) : Graded W A B := ⟨fun _ => 1, f⟩
def kleisliComp (f : A → W × B) (g : B → W × D) : A → W × D :=
  fun a => ((f a).1 * (g (f a).2).1, (g (f a).2).2)

theorem encode_comp (f : Graded W A B) (g : Graded W B D) :
    encode (comp f g) = kleisliComp (encode f) (encode g) := rfl

theorem encode_pure (f : A → B) : encode (pure (W := W) f) = (fun a => (1,f a)) := rfl

theorem assoc {F : Type u} (f : Graded W A B) (g : Graded W B D) (h : Graded W D F) :
    comp (comp f g) h = comp f (comp g h) := by
  cases f; cases g; cases h
  simp only [comp, mul_assoc]

theorem left_unit (f : Graded W A B) : comp (pure id) f = f := by
  cases f; simp [comp, pure]
theorem right_unit (f : Graded W A B) : comp f (pure id) = f := by
  cases f; simp [comp, pure]

/-- Grade equality and body commutation are both retained. -/
def Square (f : Graded W A B) (g : Graded W A' B') (a : A → A') (b : B → B') : Prop :=
  (∀ x, f.grade x = g.grade (a x)) ∧ (∀ x, b (f.body x) = g.body (a x))
def KleisliSquare (f : A → W × B) (g : A' → W × B') (a : A → A') (b : B → B') : Prop :=
  ∀ x, ((f x).1, b (f x).2) = g (a x)

omit [Monoid W] in
theorem square_iff (f : Graded W A B) (g : Graded W A' B') (a : A → A') (b : B → B') :
    Square f g a b ↔ KleisliSquare (encode f) (encode g) a b := by
  constructor
  · intro ⟨hg,hb⟩ x
    exact Prod.ext (hg x) (hb x)
  · intro h
    exact ⟨fun x => congrArg Prod.fst (h x), fun x => congrArg Prod.snd (h x)⟩

theorem horizontal {f : Graded W A B} {g : Graded W B D}
    {f' : Graded W A' B'} {g' : Graded W B' D'} {a : A → A'} {b : B → B'} {d : D → D'}
    (hf : Square f f' a b) (hg : Square g g' b d) :
    Square (comp f g) (comp f' g') a d := by
  constructor
  · intro x
    change f.grade x * g.grade (f.body x) = f'.grade (a x) * g'.grade (f'.body (a x))
    rw [hf.1 x, hg.1 (f.body x), hf.2 x]
  · intro x
    change d (g.body (f.body x)) = g'.body (f'.body (a x))
    rw [hg.2 (f.body x), hf.2 x]
end Writer
end ContextualComposition
