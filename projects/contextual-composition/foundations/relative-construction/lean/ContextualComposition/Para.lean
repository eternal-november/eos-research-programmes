module

public import Mathlib.CategoryTheory.Category.Basic

@[expose] public section

/-! Forward-reparameterized Para on the cartesian action of Type.
Noninvertible parameter maps are retained as native cells. -/
namespace ContextualComposition.Para
universe u
structure Arrow (A B : Type u) where
  Param : Type u
  body : A × Param → B

structure Square {A B A' B' : Type u} (f : Arrow A B) (g : Arrow A' B')
    (a : A → A') (b : B → B') where
  param : f.Param → g.Param
  comm : ∀ x p, b (f.body (x,p)) = g.body (a x,param p)

variable {A B D F A' B' D' : Type u}
def identity (f : Arrow A B) : Square f f id id := ⟨id, fun _ _ => rfl⟩
def vertical {A'' B'' : Type u} {f : Arrow A B} {g : Arrow A' B'} {h : Arrow A'' B''}
    {a : A → A'} {b : B → B'} {a' : A' → A''} {b' : B' → B''}
    (s : Square f g a b) (t : Square g h a' b') : Square f h (a' ∘ a) (b' ∘ b) where
  param := t.param ∘ s.param
  comm x p := by
    change b' (b (f.body (x,p))) = h.body (a' (a x),t.param (s.param p))
    rw [s.comm, t.comm]

@[ext] theorem square_ext {f : Arrow A B} {g : Arrow A' B'} {a : A → A'} {b : B → B'}
    {s t : Square f g a b} (h : s.param = t.param) : s = t := by
  cases s; cases t; cases h; rfl

instance : CategoryTheory.Category (Arrow A B) where
  Hom f g := Square f g id id
  id := identity
  comp := vertical
  id_comp _ := by apply square_ext; rfl
  comp_id _ := by apply square_ext; rfl
  assoc _ _ _ := by apply square_ext; rfl

def comp (f : Arrow A B) (g : Arrow B D) : Arrow A D where
  Param := f.Param × g.Param
  body x := g.body (f.body (x.1,x.2.1),x.2.2)

def horizontal {f : Arrow A B} {g : Arrow B D} {f' : Arrow A' B'} {g' : Arrow B' D'}
    {a : A → A'} {b : B → B'} {d : D → D'}
    (s : Square f f' a b) (t : Square g g' b d) :
    Square (comp f g) (comp f' g') a d where
  param pq := (s.param pq.1,t.param pq.2)
  comm x pq := by
    change d (g.body (f.body (x,pq.1),pq.2)) = g'.body (f'.body (a x,s.param pq.1),t.param pq.2)
    rw [t.comm, s.comm]

theorem horizontal_identity (f : Arrow A B) (g : Arrow B D) :
    horizontal (identity f) (identity g) = identity (comp f g) := by
  apply square_ext; rfl

theorem interchange {A'' B'' D'' : Type u}
    {f : Arrow A B} {g : Arrow B D} {f' : Arrow A' B'} {g' : Arrow B' D'}
    {f'' : Arrow A'' B''} {g'' : Arrow B'' D''}
    {a : A → A'} {b : B → B'} {d : D → D'}
    {a' : A' → A''} {b' : B' → B''} {d' : D' → D''}
    (s : Square f f' a b) (t : Square g g' b d)
    (s' : Square f' f'' a' b') (t' : Square g' g'' b' d') :
    horizontal (vertical s s') (vertical t t') = vertical (horizontal s t) (horizontal s' t') := by
  apply square_ext; rfl

def assocForward (f : Arrow A B) (g : Arrow B D) (h : Arrow D F) :
    Square (comp (comp f g) h) (comp f (comp g h)) id id :=
  ⟨fun p => (p.1.1,(p.1.2,p.2)), fun _ _ => rfl⟩
def assocBackward (f : Arrow A B) (g : Arrow B D) (h : Arrow D F) :
    Square (comp f (comp g h)) (comp (comp f g) h) id id :=
  ⟨fun p => ((p.1,p.2.1),p.2.2), fun _ _ => rfl⟩
theorem assoc_inverse (f : Arrow A B) (g : Arrow B D) (h : Arrow D F) :
    vertical (assocForward f g h) (assocBackward f g h) = identity _ := by
  apply square_ext; rfl

theorem assoc_inverse_other (f : Arrow A B) (g : Arrow B D) (h : Arrow D F) :
    vertical (assocBackward f g h) (assocForward f g h) = identity _ := by
  apply square_ext; rfl

theorem assoc_naturality {F' : Type u}
    {f : Arrow A B} {g : Arrow B D} {h : Arrow D F}
    {f' : Arrow A' B'} {g' : Arrow B' D'} {h' : Arrow D' F'}
    {a : A → A'} {b : B → B'} {d : D → D'} {e : F → F'}
    (s : Square f f' a b) (t : Square g g' b d) (r : Square h h' d e) :
    vertical (horizontal (horizontal s t) r) (assocForward f' g' h') =
      vertical (assocForward f g h) (horizontal s (horizontal t r)) := by
  apply square_ext; rfl

theorem pentagon {G : Type u} (f : Arrow A B) (g : Arrow B D) (h : Arrow D F) (k : Arrow F G) :
    vertical (assocForward (comp f g) h k) (assocForward f g (comp h k)) =
      vertical (vertical (horizontal (assocForward f g h) (identity k))
        (assocForward f (comp g h) k)) (horizontal (identity f) (assocForward g h k)) := by
  apply square_ext; rfl

def pure (f : A → B) : Arrow A B := ⟨PUnit,fun x => f x.1⟩
def leftUnitor (f : Arrow A B) : Square (comp (pure id) f) f id id :=
  ⟨Prod.snd, fun _ _ => rfl⟩
def rightUnitor (f : Arrow A B) : Square (comp f (pure id)) f id id :=
  ⟨Prod.fst, fun _ _ => rfl⟩
def leftUnitorInv (f : Arrow A B) : Square f (comp (pure id) f) id id :=
  ⟨fun p => (PUnit.unit,p), fun _ _ => rfl⟩
def rightUnitorInv (f : Arrow A B) : Square f (comp f (pure id)) id id :=
  ⟨fun p => (p,PUnit.unit), fun _ _ => rfl⟩

theorem left_unitor_inverse (f : Arrow A B) :
    vertical (leftUnitor f) (leftUnitorInv f) = identity _ := by
  apply square_ext; rfl

theorem left_unitor_inverse_other (f : Arrow A B) :
    vertical (leftUnitorInv f) (leftUnitor f) = identity _ := by
  apply square_ext; rfl

theorem right_unitor_inverse (f : Arrow A B) :
    vertical (rightUnitor f) (rightUnitorInv f) = identity _ := by
  apply square_ext; rfl

theorem right_unitor_inverse_other (f : Arrow A B) :
    vertical (rightUnitorInv f) (rightUnitor f) = identity _ := by
  apply square_ext; rfl

theorem triangle (f : Arrow A B) (g : Arrow B D) :
    vertical (assocForward f (pure id) g) (horizontal (identity f) (leftUnitor g)) =
      horizontal (rightUnitor f) (identity g) := by
  apply square_ext; rfl

/-- A forward cell may collapse parameters; invertibility is not built into the native hom. -/
def collapse : Square (⟨Bool,fun _ => PUnit.unit⟩ : Arrow PUnit PUnit)
    (⟨PUnit,fun _ => PUnit.unit⟩ : Arrow PUnit PUnit) id id :=
  ⟨fun _ => PUnit.unit,fun _ _ => rfl⟩
theorem collapse_not_injective : ¬ Function.Injective collapse.param := by
  intro h
  have hf : false = true := h rfl
  cases hf
end ContextualComposition.Para
